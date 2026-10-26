import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w7_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-772765011/372765011)*δ^0*p^1
def w7_dn_minimum : ℝ := 1463825055/745530022
def w7_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)]]
theorem w7_dn_lower (i : Fin 3) (j : Fin 4) :
    w7_dn_minimum ≤ w7_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_dn_minimum,w7_dn_table]
theorem w7_dn_identity (δ p : ℝ) :
    w7_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_dn_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_dn_table,Fin.sum_univ_succ]
  ring
theorem w7_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_dn_power δ p := by
  rw [w7_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_dn_lower
theorem w7_dn_binding (δ p : ℝ) :
    w7_dn_power δ p=guardD Plane.C δ p := by
  norm_num [w7_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-400000000/372765011)*δ^0*p^1
def w7_aa_minimum : ℝ := 545530022/372765011
def w7_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)]]
theorem w7_aa_lower (i : Fin 3) (j : Fin 4) :
    w7_aa_minimum ≤ w7_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_aa_minimum,w7_aa_table]
theorem w7_aa_identity (δ p : ℝ) :
    w7_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_aa_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_aa_table,Fin.sum_univ_succ]
  ring
theorem w7_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_aa_power δ p := by
  rw [w7_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_aa_lower
theorem w7_aa_binding (δ p : ℝ) :
    w7_aa_power δ p=guardA Plane.C δ p := by
  norm_num [w7_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-195798850/372765011)*δ^0*p^1
def w7_cc_minimum : ℝ := 274865586/372765011
def w7_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)]]
theorem w7_cc_lower (i : Fin 3) (j : Fin 4) :
    w7_cc_minimum ≤ w7_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_cc_minimum,w7_cc_table]
theorem w7_cc_identity (δ p : ℝ) :
    w7_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_cc_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_cc_table,Fin.sum_univ_succ]
  ring
theorem w7_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_cc_power δ p := by
  rw [w7_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_cc_lower
theorem w7_cc_binding (δ p : ℝ) :
    w7_cc_power δ p=guardC Plane.C δ p := by
  norm_num [w7_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-1287941685/745530022)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (400000000/372765011)*δ^1*p^2
def w7_j_minimum : ℝ := 25260909305/23856960704
def w7_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(26367482778623/24429527760896:ℝ), (13129618117817/12214763880448:ℝ), (26151236567645/24429527760896:ℝ), (406929433979/381711371264:ℝ)],
  ![(52558580580943/48859055521792:ℝ), (26171054239977/24429527760896:ℝ), (52126133253965/48859055521792:ℝ), (811103982859/763422742528:ℝ)],
  ![(1636943612645/1526845485056:ℝ), (815089757635/763422742528:ℝ), (1623431042895/1526845485056:ℝ), (25260909305/23856960704:ℝ)]]
theorem w7_j_lower (i : Fin 3) (j : Fin 4) :
    w7_j_minimum ≤ w7_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_j_minimum,w7_j_table]
theorem w7_j_identity (δ p : ℝ) :
    w7_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_j_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_j_table,Fin.sum_univ_succ]
  ring
theorem w7_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_j_power δ p := by
  rw [w7_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_j_lower
theorem w7_j_binding (δ p : ℝ) :
    w7_j_power δ p=guardJ Plane.C δ p := by
  norm_num [w7_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-568563861/372765011)*δ^1*p^1 +
  (195798850/372765011)*δ^1*p^2
def w7_tlo_minimum : ℝ := 32571571941/190855685632
def w7_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(272503619191245/1563489776697344:ℝ), (270603451186479/1563489776697344:ℝ), (4198609644317/24429527760896:ℝ), (32571571941/190855685632:ℝ)],
  ![(548456651283645/3126979553394688:ℝ), (544632262514559/3126979553394688:ℝ), (8450366246157/48859055521792:ℝ), (65555442261/381711371264:ℝ)],
  ![(17247064505775/97718111043584:ℝ), (17126800708005/97718111043584:ℝ), (265734787615/1526845485056:ℝ), (2061491895/11928480352:ℝ)]]
theorem w7_tlo_lower (i : Fin 3) (j : Fin 4) :
    w7_tlo_minimum ≤ w7_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_tlo_minimum,w7_tlo_table]
theorem w7_tlo_identity (δ p : ℝ) :
    w7_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_tlo_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_tlo_table,Fin.sum_univ_succ]
  ring
theorem w7_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_tlo_power δ p := by
  rw [w7_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_tlo_lower
theorem w7_tlo_binding (δ p : ℝ) :
    w7_tlo_power δ p=guardTLo Plane.C δ p := by
  norm_num [w7_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-643713254163/1491060044000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (4754098847511/3727650110000)*δ^1*p^1 +
  (-95838850/372765011)*δ^1*p^2
def w7_thi_minimum : ℝ := 1116694607178009/12214763880448000
def w7_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(93254595860587383/977181110435840000:ℝ), (93360168419848089/977181110435840000:ℝ), (4673168747874971/48859055521792000:ℝ), (365485216693521/3817113712640000:ℝ)],
  ![(182590164434828103/1954362220871680000:ℝ), (182816552294020809/1954362220871680000:ℝ), (9151908908017707/97718111043584000:ℝ), (715840007944641/7634227425280000:ℝ)],
  ![(1116694607178009/12214763880448000:ℝ), (1118204798427159/12214763880448000:ℝ), (279921260008921/3053690970112000:ℝ), (4379434890639/47713921408000:ℝ)]]
theorem w7_thi_lower (i : Fin 3) (j : Fin 4) :
    w7_thi_minimum ≤ w7_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_thi_minimum,w7_thi_table]
theorem w7_thi_identity (δ p : ℝ) :
    w7_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_thi_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_thi_table,Fin.sum_univ_succ]
  ring
theorem w7_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_thi_power δ p := by
  rw [w7_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_thi_lower
theorem w7_thi_binding (δ p : ℝ) :
    w7_thi_power δ p=guardTHi Plane.C δ p := by
  norm_num [w7_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-24310471945/27584610814)*δ^0*p^1 +
  (2301650128018533120/5141288876755714477)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-55163398065/13792305407)*δ^1*p^1 +
  (15893629311901003644/5141288876755714477)*δ^1*p^2 +
  (-4327484061600000000/5141288876755714477)*δ^1*p^3
def w7_rlo_minimum : ℝ := 1346120312728987519185/5264679809797851624448
def w7_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2854261660691379783366871/10782064250466000126869504:ℝ), (8464522011940980296194355/32346192751398000380608512:ℝ), (261472398589699028240027/1010818523481187511894016:ℝ), (1346120312728987519185/5264679809797851624448:ℝ)],
  ![(5742944468148292055852711/21564128500932000253739008:ℝ), (17031533447536276612320835/64692385502796000761217024:ℝ), (526123626394507586747947/2021637046962375023788032:ℝ), (2708673356238428902785/10529359619595703248896:ℝ)],
  ![(180542675466057017030365/673879015654125007929344:ℝ), (535438214724706019757905/2021637046962375023788032:ℝ), (16540701737800534906745/63176157717574219493376:ℝ), (85159565219340086475/329042488112365726528:ℝ)]]
theorem w7_rlo_lower (i : Fin 3) (j : Fin 4) :
    w7_rlo_minimum ≤ w7_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_rlo_minimum,w7_rlo_table]
theorem w7_rlo_identity (δ p : ℝ) :
    w7_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_rlo_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_rlo_table,Fin.sum_univ_succ]
  ring
theorem w7_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_rlo_power δ p := by
  rw [w7_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_rlo_lower
theorem w7_rlo_binding (δ p : ℝ) :
    w7_rlo_power δ p=guardRLo Plane.C δ p := by
  norm_num [w7_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-2266935935/745530022)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (1360161561/372765011)*δ^1*p^1 +
  (-151306500474037350/138953753425830121)*δ^1*p^2
def w7_rhi_minimum : ℝ := 2347071600673667175/4446520109626563872
def w7_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(316911752958904073066377/582814283808972979830784:ℝ), (946388665717925470794569/1748442851426918939492352:ℝ), (14719631585295838702063/27319419553545608429568:ℝ), (38156678308094760645/71144321754025021952:ℝ)],
  ![(628810841986999470108857/1165628567617945959661568:ℝ), (1877808090677570925355129/3496885702853837878984704:ℝ), (29206439472405978725183/54638839107091216859136:ℝ), (75709823918873435445/142288643508050043904:ℝ)],
  ![(19493693064255962315155/36425892738060811239424:ℝ), (58213714059977840910035/109277678214182433718272:ℝ), (905425492944383751445/1707463722096600526848:ℝ), (2347071600673667175/4446520109626563872:ℝ)]]
theorem w7_rhi_lower (i : Fin 3) (j : Fin 4) :
    w7_rhi_minimum ≤ w7_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_rhi_minimum,w7_rhi_table]
theorem w7_rhi_identity (δ p : ℝ) :
    w7_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_rhi_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_rhi_table,Fin.sum_univ_succ]
  ring
theorem w7_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_rhi_power δ p := by
  rw [w7_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_rhi_lower
theorem w7_rhi_binding (δ p : ℝ) :
    w7_rhi_power δ p=guardRHi Plane.C δ p := by
  norm_num [w7_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_mlo_power (δ p : ℝ) : ℝ := (-612155921/1000000000)*δ^0*p^0 +
  (234921084425093377/186382505500000000)*δ^0*p^1 +
  (-80408245463812802801144049/138953753425830121000000000)*δ^0*p^2 +
  (3112155921/2500000000)*δ^1*p^0 +
  (-1218644907274906623/465956263750000000)*δ^1*p^1 +
  (1353886465924906623/931912527500000000)*δ^1*p^2 +
  (-576042239150560242/3473843835645753025)*δ^1*p^3
def w7_mlo_minimum : ℝ := 6308190832355846456282070398909/2914071419044864899153920000000000
def w7_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(6308190832355846456282070398909/2914071419044864899153920000000000:ℝ), (20890851662828092253440265914537/8742214257134594697461760000000000:ℝ), (178544214551193597624819267721/68298548883864021073920000000000:ℝ), (403852147180649022358342917/142288643508050043904000000000:ℝ)],
  ![(17564297720834944405762793079469/5828142838089729798307840000000000:ℝ), (56451267509548106376249525648857/17484428514269189394923520000000000:ℝ), (470343421877493095884305114041/136597097767728042147840000000000:ℝ), (1040858083294202678307575157/284577287016100087808000000000:ℝ)],
  ![(140701336105988724368509033507/36425892738060811239424000000000:ℝ), (444505198084000176535115746679/109277678214182433718272000000000:ℝ), (3647490091578743728243573079/853731861048300263424000000000:ℝ), (7962574201419420699365403/1778608043850625548800000000:ℝ)]]
theorem w7_mlo_lower (i : Fin 3) (j : Fin 4) :
    w7_mlo_minimum ≤ w7_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_mlo_minimum,w7_mlo_table]
theorem w7_mlo_identity (δ p : ℝ) :
    w7_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_mlo_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_mlo_table,Fin.sum_univ_succ]
  ring
theorem w7_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_mlo_power δ p := by
  rw [w7_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_mlo_lower
theorem w7_mlo_binding (δ p : ℝ) :
    w7_mlo_power δ p=guardMLo Plane.C δ p := by
  norm_num [w7_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-6287390142794251/4659562637500000)*δ^0*p^1 +
  (2116941220965473617000587/3473843835645753025000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (30373484644705749/11648906593750000)*δ^1*p^1 +
  (-32789348625955749/23297813187500000)*δ^1*p^2 +
  (101948830800770718/694768767129150605)*δ^1*p^3
def w7_mhi_minimum : ℝ := 594042492771717371031111/44465201096265638720000000
def w7_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2355560280318685627121956949591/145703570952243244957696000000000:ℝ), (3456810014987865470269089302669/218555356428364867436544000000000:ℝ), (26410456762602460151032194077/1707463722096600526848000000000:ℝ), (53784714372192022071504729/3557216087701251097600000000:ℝ)],
  ![(4445857335570853751868607509031/291407141904486489915392000000000:ℝ), (6520156068003516782498517200509/437110712856729734873088000000000:ℝ), (49781350169797984350171035917/3414927444193201053696000000000:ℝ), (101308113793929411753993609/7114432175402502195200000000:ℝ)],
  ![(26128713190652101559333131993/1821294636903040561971200000000:ℝ), (38291825662695641402867848723/2731941955354560842956800000000:ℝ), (292136167589944052489235523/21343296526207506585600000000:ℝ), (594042492771717371031111/44465201096265638720000000:ℝ)]]
theorem w7_mhi_lower (i : Fin 3) (j : Fin 4) :
    w7_mhi_minimum ≤ w7_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_mhi_minimum,w7_mhi_table]
theorem w7_mhi_identity (δ p : ℝ) :
    w7_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_mhi_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_mhi_table,Fin.sum_univ_succ]
  ring
theorem w7_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_mhi_power δ p := by
  rw [w7_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_mhi_lower
theorem w7_mhi_binding (δ p : ℝ) :
    w7_mhi_power δ p=guardMHi Plane.C δ p := by
  norm_num [w7_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_widthlo_power (δ p : ℝ) : ℝ := (5565906092767/8000000000000)*δ^0*p^0 +
  (-2051607364334019258479/1491060044000000000000)*δ^0*p^1 +
  (687632641159884323317578759423/1111630027406640968000000000000)*δ^0*p^2 +
  (-25565906092767/20000000000000)*δ^1*p^0 +
  (9710652314219380741521/3727650110000000000000)*δ^1*p^1 +
  (-10391389548559180741521/7455300220000000000000)*δ^1*p^2 +
  (979845789367848241521/6947687671291506050000)*δ^1*p^3
def w7_widthlo_minimum : ℝ := 265970909504987481010354249419/14228864350805004390400000000000
def w7_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(504656799173246693292888641534907857/23312571352358919193231360000000000000:ℝ), (1486861825154054776663403266799686201/69937714057076757579694080000000000000:ℝ), (11405098039369588718967704558068633/546388391070912168591360000000000000:ℝ), (23322668396327491368161886457941/1138309148064400351232000000000000:ℝ)],
  ![(966016785409464276022075942739588737/46625142704717838386462720000000000000:ℝ), (2845258389099241608231262403438291561/139875428114153515159388160000000000000:ℝ), (21817618203100828655216572502849993/1092776782141824337182720000000000000:ℝ), (44600341156726489848990226411461/2276618296128800702464000000000000:ℝ)],
  ![(5766999827952719784114841265058511/291407141904486489915392000000000000:ℝ), (16979957049314835394598239207982567/874221425713459469746176000000000000:ℝ), (130156502046640499203110849309767/6829854888386402107392000000000000:ℝ), (265970909504987481010354249419/14228864350805004390400000000000:ℝ)]]
theorem w7_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w7_widthlo_minimum ≤ w7_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_widthlo_minimum,w7_widthlo_table]
theorem w7_widthlo_identity (δ p : ℝ) :
    w7_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_widthlo_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w7_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_widthlo_power δ p := by
  rw [w7_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_widthlo_lower
theorem w7_widthlo_binding (δ p : ℝ) :
    w7_widthlo_power δ p=guardWidth Plane.C δ p := by
  norm_num [w7_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-3899358951306417/4659562637500000)*δ^1*p^1 +
  (35812707313/111829503300)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (18756998265080749/11648906593750000)*δ^2*p^1 +
  (-70580026487/93191252750)*δ^2*p^2 +
  (27200000/372765011)*δ^2*p^3
def w7_tail_minimum : ℝ := 3795135387532803/954278428160000000
def w7_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(30516010722720655968481/6253959106789376000000000:ℝ), (29786097130735746873523/6253959106789376000000000:ℝ), (1089650035695610959079/234523466504601600000000:ℝ), (27665789854316889843/6107381940224000000000:ℝ)],
  ![(359553091543819132551/78174488834867200000000:ℝ), (14024991208776884109/3126979553394688000000:ℝ), (21356846444365134439/4885905552179200000000:ℝ), (325007783594361477/76342274252800000000:ℝ)],
  ![(4213007168915681297/977181110435840000000:ℝ), (4103928560155895747/977181110435840000000:ℝ), (749061854855154451/183221458206720000000:ℝ), (3795135387532803/954278428160000000:ℝ)]]
theorem w7_tail_lower (i : Fin 3) (j : Fin 4) :
    w7_tail_minimum ≤ w7_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_tail_minimum,w7_tail_table]
theorem w7_tail_identity (δ p : ℝ) :
    w7_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_tail_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_tail_table,Fin.sum_univ_succ]
  ring
theorem w7_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_tail_power δ p := by
  rw [w7_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_tail_lower
theorem w7_tail_binding (δ p : ℝ) :
    w7_tail_power δ p=guardTail Plane.C δ p := by
  norm_num [w7_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w7_monotone_power (δ p : ℝ) : ℝ := (777438810/372765011)*δ^0*p^0 +
  (-978994250/372765011)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-941328872/372765011)*δ^1*p^0 +
  (1191597700/372765011)*δ^1*p^1 +
  (-154438583925962650/138953753425830121)*δ^1*p^2
def w7_monotone_minimum : ℝ := 3864499017414517105/8893040219253127744
def w7_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(260823701426768914961847/582814283808972979830784:ℝ), (779011529094802838151991/1748442851426918939492352:ℝ), (6059108841071912756347/13659709776772804214784:ℝ), (62836451169231179107/142288643508050043904:ℝ)],
  ![(517477243321370978837127/1165628567617945959661568:ℝ), (1545568674399254746445831/3496885702853837878984704:ℝ), (12021354239627597423627/27319419553545608429568:ℝ), (124668435447863452787/284577287016100087808:ℝ)],
  ![(16040846368412628992205/36425892738060811239424:ℝ), (47909821581528244268365/109277678214182433718272:ℝ), (372640337409730291705/853731861048300263424:ℝ), (3864499017414517105/8893040219253127744:ℝ)]]
theorem w7_monotone_lower (i : Fin 3) (j : Fin 4) :
    w7_monotone_minimum ≤ w7_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w7_monotone_minimum,w7_monotone_table]
theorem w7_monotone_identity (δ p : ℝ) :
    w7_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w7_monotone_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w7_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w7_monotone_table,Fin.sum_univ_succ]
  ring
theorem w7_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w7_monotone_power δ p := by
  rw [w7_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w7_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w7_monotone_lower
theorem w7_monotone_binding (δ p : ℝ) :
    w7_monotone_power δ p=guardMonotone Plane.C δ p := by
  norm_num [w7_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window7_admissible (δ p : ℝ) (ha : window7.Available δ p) :
    Admissible window7.plane δ p := by
  have hd : δ ∈ Set.Icc (237/512:ℝ) (15/32) := ha.1
  have hp : p ∈ Set.Icc (63/128:ℝ) (1/2) := ha.2
  change Admissible Plane.C δ p
  constructor
  · rw [←w7_dn_binding]
    exact w7_dn_positive hd hp
  · rw [←w7_aa_binding]
    exact w7_aa_positive hd hp
  · rw [←w7_cc_binding]
    exact w7_cc_positive hd hp
  · rw [←w7_j_binding]
    exact w7_j_positive hd hp
  · rw [←w7_tlo_binding]
    exact w7_tlo_positive hd hp
  · rw [←w7_thi_binding]
    exact w7_thi_positive hd hp
  · rw [←w7_rlo_binding]
    exact w7_rlo_positive hd hp
  · rw [←w7_rhi_binding]
    exact w7_rhi_positive hd hp
  · rw [←w7_mlo_binding]
    exact w7_mlo_positive hd hp
  · rw [←w7_mhi_binding]
    exact w7_mhi_positive hd hp
  · rw [←w7_widthlo_binding]
    exact w7_widthlo_positive hd hp
  · rw [←w7_tail_binding]
    exact w7_tail_positive hd hp
  · rw [←w7_monotone_binding]
    exact w7_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window7_admissible
