import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w8_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-772765011/372765011)*δ^0*p^1
def w8_dn_minimum : ℝ := 1463825055/745530022
def w8_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)]]
theorem w8_dn_lower (i : Fin 3) (j : Fin 4) :
    w8_dn_minimum ≤ w8_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_dn_minimum,w8_dn_table]
theorem w8_dn_identity (δ p : ℝ) :
    w8_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_dn_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_dn_table,Fin.sum_univ_succ]
  ring
theorem w8_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_dn_power δ p := by
  rw [w8_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_dn_lower
theorem w8_dn_binding (δ p : ℝ) :
    w8_dn_power δ p=guardD Plane.C δ p := by
  norm_num [w8_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-400000000/372765011)*δ^0*p^1
def w8_aa_minimum : ℝ := 545530022/372765011
def w8_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)]]
theorem w8_aa_lower (i : Fin 3) (j : Fin 4) :
    w8_aa_minimum ≤ w8_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_aa_minimum,w8_aa_table]
theorem w8_aa_identity (δ p : ℝ) :
    w8_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_aa_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_aa_table,Fin.sum_univ_succ]
  ring
theorem w8_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_aa_power δ p := by
  rw [w8_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_aa_lower
theorem w8_aa_binding (δ p : ℝ) :
    w8_aa_power δ p=guardA Plane.C δ p := by
  norm_num [w8_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-195798850/372765011)*δ^0*p^1
def w8_cc_minimum : ℝ := 274865586/372765011
def w8_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)]]
theorem w8_cc_lower (i : Fin 3) (j : Fin 4) :
    w8_cc_minimum ≤ w8_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_cc_minimum,w8_cc_table]
theorem w8_cc_identity (δ p : ℝ) :
    w8_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_cc_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_cc_table,Fin.sum_univ_succ]
  ring
theorem w8_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_cc_power δ p := by
  rw [w8_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_cc_lower
theorem w8_cc_binding (δ p : ℝ) :
    w8_cc_power δ p=guardC Plane.C δ p := by
  norm_num [w8_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-1287941685/745530022)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (400000000/372765011)*δ^1*p^2
def w8_j_minimum : ℝ := 199332389341/190855685632
def w8_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1636943612645/1526845485056:ℝ), (815089757635/763422742528:ℝ), (1623431042895/1526845485056:ℝ), (25260909305/23856960704:ℝ)],
  ![(26014712826017/24429527760896:ℝ), (12953254126503/12214763880448:ℝ), (25798556804995/24429527760896:ℝ), (401419663781/381711371264:ℝ)],
  ![(12919163924857/12214763880448:ℝ), (6432536065423/6107381940224:ℝ), (12811108461835/12214763880448:ℝ), (199332389341/190855685632:ℝ)]]
theorem w8_j_lower (i : Fin 3) (j : Fin 4) :
    w8_j_minimum ≤ w8_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_j_minimum,w8_j_table]
theorem w8_j_identity (δ p : ℝ) :
    w8_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_j_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_j_table,Fin.sum_univ_succ]
  ring
theorem w8_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_j_power δ p := by
  rw [w8_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_j_lower
theorem w8_j_binding (δ p : ℝ) :
    w8_j_power δ p=guardJ Plane.C δ p := by
  norm_num [w8_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-568563861/372765011)*δ^1*p^1 +
  (195798850/372765011)*δ^1*p^2
def w8_tlo_minimum : ℝ := 2061491895/11928480352
def w8_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(17247064505775/97718111043584:ℝ), (17126800708005/97718111043584:ℝ), (265734787615/1526845485056:ℝ), (2061491895/11928480352:ℝ)],
  ![(279402444993555/1563489776697344:ℝ), (277454171469681/1563489776697344:ℝ), (4304903559363/24429527760896:ℝ), (33396168699/190855685632:ℝ)],
  ![(141425928947355/781744888348672:ℝ), (140439765805641/781744888348672:ℝ), (2179025258443/12214763880448:ℝ), (16904233539/95427842816:ℝ)]]
theorem w8_tlo_lower (i : Fin 3) (j : Fin 4) :
    w8_tlo_minimum ≤ w8_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_tlo_minimum,w8_tlo_table]
theorem w8_tlo_identity (δ p : ℝ) :
    w8_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_tlo_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_tlo_table,Fin.sum_univ_succ]
  ring
theorem w8_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_tlo_power δ p := by
  rw [w8_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_tlo_lower
theorem w8_tlo_binding (δ p : ℝ) :
    w8_tlo_power δ p=guardTLo Plane.C δ p := by
  norm_num [w8_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-643713254163/1491060044000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (4754098847511/3727650110000)*δ^1*p^1 +
  (-95838850/372765011)*δ^1*p^2
def w8_thi_minimum : ℝ := 40748757000773697/488590555217920000
def w8_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1116694607178009/12214763880448000:ℝ), (1118204798427159/12214763880448000:ℝ), (279921260008921/3053690970112000:ℝ), (4379434890639/47713921408000:ℝ)],
  ![(85416541287894057/977181110435840000:ℝ), (85552599328497351/977181110435840000:ℝ), (4284311572410501/48859055521792000:ℝ), (335224365808719/3817113712640000:ℝ)],
  ![(40748757000773697/488590555217920000:ℝ), (40824407391410991/488590555217920000:ℝ), (2044941492339133/24429527760896000:ℝ), (160046970183159/1908556856320000:ℝ)]]
theorem w8_thi_lower (i : Fin 3) (j : Fin 4) :
    w8_thi_minimum ≤ w8_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_thi_minimum,w8_thi_table]
theorem w8_thi_identity (δ p : ℝ) :
    w8_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_thi_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_thi_table,Fin.sum_univ_succ]
  ring
theorem w8_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_thi_power δ p := by
  rw [w8_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_thi_lower
theorem w8_thi_binding (δ p : ℝ) :
    w8_thi_power δ p=guardTHi Plane.C δ p := by
  norm_num [w8_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-24310471945/27584610814)*δ^0*p^1 +
  (2301650128018533120/5141288876755714477)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-55163398065/13792305407)*δ^1*p^1 +
  (15893629311901003644/5141288876755714477)*δ^1*p^2 +
  (-4327484061600000000/5141288876755714477)*δ^1*p^3
def w8_rlo_minimum : ℝ := 85159565219340086475/329042488112365726528
def w8_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(180542675466057017030365/673879015654125007929344:ℝ), (535438214724706019757905/2021637046962375023788032:ℝ), (16540701737800534906745/63176157717574219493376:ℝ), (85159565219340086475/329042488112365726528:ℝ)],
  ![(2923103954222444761604809/10782064250466000126869504:ℝ), (8669500859249612336058605/32346192751398000380608512:ℝ), (267830057019918088775813/1010818523481187511894016:ℝ), (1378985774289895248015/5264679809797851624448:ℝ)],
  ![(1478762550493988625361889/5391032125233000063434752:ℝ), (118540409228431464270145/437110712856729734873088:ℝ), (135504443117513809521853/505409261740593755947008:ℝ), (697709252535174556215/2632339904898925812224:ℝ)]]
theorem w8_rlo_lower (i : Fin 3) (j : Fin 4) :
    w8_rlo_minimum ≤ w8_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_rlo_minimum,w8_rlo_table]
theorem w8_rlo_identity (δ p : ℝ) :
    w8_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_rlo_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_rlo_table,Fin.sum_univ_succ]
  ring
theorem w8_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_rlo_power δ p := by
  rw [w8_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_rlo_lower
theorem w8_rlo_binding (δ p : ℝ) :
    w8_rlo_power δ p=guardRLo Plane.C δ p := by
  norm_num [w8_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-2266935935/745530022)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (1360161561/372765011)*δ^1*p^1 +
  (-151306500474037350/138953753425830121)*δ^1*p^2
def w8_rhi_minimum : ℝ := 18173040108073251555/35572160877012510976
def w8_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(19493693064255962315155/36425892738060811239424:ℝ), (58213714059977840910035/109277678214182433718272:ℝ), (905425492944383751445/1707463722096600526848:ℝ), (2347071600673667175/4446520109626563872:ℝ)],
  ![(306886425097286721018583/582814283808972979830784:ℝ), (916450184201365438326551/1748442851426918939492352:ℝ), (14253984188924441344177/27319419553545608429568:ℝ), (36949612913462588955/71144321754025021952:ℝ)],
  ![(150936880583239022497343/291407141904486489915392:ℝ), (450740471721542711046271/874221425713459469746176:ℝ), (7010580245369371332617/13659709776772804214784:ℝ), (18173040108073251555/35572160877012510976:ℝ)]]
theorem w8_rhi_lower (i : Fin 3) (j : Fin 4) :
    w8_rhi_minimum ≤ w8_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_rhi_minimum,w8_rhi_table]
theorem w8_rhi_identity (δ p : ℝ) :
    w8_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_rhi_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_rhi_table,Fin.sum_univ_succ]
  ring
theorem w8_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_rhi_power δ p := by
  rw [w8_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_rhi_lower
theorem w8_rhi_binding (δ p : ℝ) :
    w8_rhi_power δ p=guardRHi Plane.C δ p := by
  norm_num [w8_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_mlo_power (δ p : ℝ) : ℝ := (-612155921/1000000000)*δ^0*p^0 +
  (234921084425093377/186382505500000000)*δ^0*p^1 +
  (-80408245463812802801144049/138953753425830121000000000)*δ^0*p^2 +
  (3112155921/2500000000)*δ^1*p^0 +
  (-1218644907274906623/465956263750000000)*δ^1*p^1 +
  (1353886465924906623/931912527500000000)*δ^1*p^2 +
  (-576042239150560242/3473843835645753025)*δ^1*p^3
def w8_mlo_minimum : ℝ := 140701336105988724368509033507/36425892738060811239424000000000
def w8_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(140701336105988724368509033507/36425892738060811239424000000000:ℝ), (444505198084000176535115746679/109277678214182433718272000000000:ℝ), (3647490091578743728243573079/853731861048300263424000000000:ℝ), (7962574201419420699365403/1778608043850625548800000000:ℝ)],
  ![(16204022944602349442679374962211/2914071419044864899153920000000000:ℝ), (50229980030611935992178253554103/8742214257134594697461760000000000:ℝ), (405054200101405398894152424919/68298548883864021073920000000000:ℝ), (870159725046458289540121563/142288643508050043904000000000:ℝ)],
  ![(10575969500362800467939013621931/1457035709522432449576960000000000:ℝ), (32449772107251928930773623686943/4371107128567297348730880000000000:ℝ), (259154596438255649764409501759/34149274441932010536960000000000:ℝ), (551656756989681461565505443/71144321754025021952000000000:ℝ)]]
theorem w8_mlo_lower (i : Fin 3) (j : Fin 4) :
    w8_mlo_minimum ≤ w8_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_mlo_minimum,w8_mlo_table]
theorem w8_mlo_identity (δ p : ℝ) :
    w8_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_mlo_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_mlo_table,Fin.sum_univ_succ]
  ring
theorem w8_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_mlo_power δ p := by
  rw [w8_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_mlo_lower
theorem w8_mlo_binding (δ p : ℝ) :
    w8_mlo_power δ p=guardMLo Plane.C δ p := by
  norm_num [w8_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-6287390142794251/4659562637500000)*δ^0*p^1 +
  (2116941220965473617000587/3473843835645753025000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (30373484644705749/11648906593750000)*δ^1*p^1 +
  (-32789348625955749/23297813187500000)*δ^1*p^2 +
  (101948830800770718/694768767129150605)*δ^1*p^3
def w8_mhi_minimum : ℝ := 17500384760414062452228591/1778608043850625548800000000
def w8_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(26128713190652101559333131993/1821294636903040561971200000000:ℝ), (38291825662695641402867848723/2731941955354560842956800000000:ℝ), (292136167589944052489235523/21343296526207506585600000000:ℝ), (594042492771717371031111/44465201096265638720000000:ℝ)],
  ![(1825033830185650622371344169289/145703570952243244957696000000000:ℝ), (2669882091043437154189766493011/218555356428364867436544000000000:ℝ), (20331330051788588247245489603/1707463722096600526848000000000:ℝ), (41262084471282757293473031/3557216087701251097600000000:ℝ)],
  ![(779885302559566559998018889569/72851785476121622478848000000000:ℝ), (1138209064535611498075052544091/109277678214182433718272000000000:ℝ), (8645883348190826147676068683/853731861048300263424000000000:ℝ), (17500384760414062452228591/1778608043850625548800000000:ℝ)]]
theorem w8_mhi_lower (i : Fin 3) (j : Fin 4) :
    w8_mhi_minimum ≤ w8_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_mhi_minimum,w8_mhi_table]
theorem w8_mhi_identity (δ p : ℝ) :
    w8_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_mhi_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_mhi_table,Fin.sum_univ_succ]
  ring
theorem w8_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_mhi_power δ p := by
  rw [w8_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_mhi_lower
theorem w8_mhi_binding (δ p : ℝ) :
    w8_mhi_power δ p=guardMHi Plane.C δ p := by
  norm_num [w8_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_widthlo_power (δ p : ℝ) : ℝ := (5565906092767/8000000000000)*δ^0*p^0 +
  (-2051607364334019258479/1491060044000000000000)*δ^0*p^1 +
  (687632641159884323317578759423/1111630027406640968000000000000)*δ^0*p^2 +
  (-25565906092767/20000000000000)*δ^1*p^0 +
  (9710652314219380741521/3727650110000000000000)*δ^1*p^1 +
  (-10391389548559180741521/7455300220000000000000)*δ^1*p^2 +
  (979845789367848241521/6947687671291506050000)*δ^1*p^3
def w8_widthlo_minimum : ℝ := 8593840744271006353080623472339/569154574032200175616000000000000
def w8_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(5766999827952719784114841265058511/291407141904486489915392000000000000:ℝ), (16979957049314835394598239207982567/874221425713459469746176000000000000:ℝ), (130156502046640499203110849309767/6829854888386402107392000000000000:ℝ), (265970909504987481010354249419/14228864350805004390400000000000:ℝ)],
  ![(418063173299188472165485960874453903/23312571352358919193231360000000000000:ℝ), (1229931302736318886472315006477524519/69937714057076757579694080000000000000:ℝ), (9419942288092891153530031331494087/546388391070912168591360000000000000:ℝ), (19232677124470505593494793449099/1138309148064400351232000000000000:ℝ)],
  ![(187383180181079680800892310272113463/11656285676179459596615680000000000000:ℝ), (550733020763725470688385438158221839/34968857028538378789847040000000000000:ℝ), (4213682206227271185405597359103407/273194195535456084295680000000000000:ℝ), (8593840744271006353080623472339/569154574032200175616000000000000:ℝ)]]
theorem w8_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w8_widthlo_minimum ≤ w8_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_widthlo_minimum,w8_widthlo_table]
theorem w8_widthlo_identity (δ p : ℝ) :
    w8_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_widthlo_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w8_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_widthlo_power δ p := by
  rw [w8_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_widthlo_lower
theorem w8_widthlo_binding (δ p : ℝ) :
    w8_widthlo_power δ p=guardWidth Plane.C δ p := by
  norm_num [w8_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-3899358951306417/4659562637500000)*δ^1*p^1 +
  (35812707313/111829503300)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (18756998265080749/11648906593750000)*δ^2*p^1 +
  (-70580026487/93191252750)*δ^2*p^2 +
  (27200000/372765011)*δ^2*p^3
def w8_tail_minimum : ℝ := 4313871372142498563/1526845485056000000000
def w8_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(4213007168915681297/977181110435840000000:ℝ), (4103928560155895747/977181110435840000000:ℝ), (749061854855154451/183221458206720000000:ℝ), (3795135387532803/954278428160000000:ℝ)],
  ![(146007768726062623089/39087244417433600000000:ℝ), (28369329399857077383/7817448883486720000000:ℝ), (8605627749841043601/2442952776089600000000:ℝ), (130408462909574883/38171137126400000000:ℝ)],
  ![(4890571984589874833041/1563489776697344000000000:ℝ), (4732721144319340976323/1563489776697344000000000:ℝ), (171562289689876418743/58630866626150400000000:ℝ), (4313871372142498563/1526845485056000000000:ℝ)]]
theorem w8_tail_lower (i : Fin 3) (j : Fin 4) :
    w8_tail_minimum ≤ w8_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_tail_minimum,w8_tail_table]
theorem w8_tail_identity (δ p : ℝ) :
    w8_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_tail_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_tail_table,Fin.sum_univ_succ]
  ring
theorem w8_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_tail_power δ p := by
  rw [w8_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_tail_lower
theorem w8_tail_binding (δ p : ℝ) :
    w8_tail_power δ p=guardTail Plane.C δ p := by
  norm_num [w8_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w8_monotone_power (δ p : ℝ) : ℝ := (777438810/372765011)*δ^0*p^0 +
  (-978994250/372765011)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-941328872/372765011)*δ^1*p^0 +
  (1191597700/372765011)*δ^1*p^1 +
  (-154438583925962650/138953753425830121)*δ^1*p^2
def w8_monotone_minimum : ℝ := 29911525248717231413/71144321754025021952
def w8_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(16040846368412628992205/36425892738060811239424:ℝ), (47909821581528244268365/109277678214182433718272:ℝ), (372640337409730291705/853731861048300263424:ℝ), (3864499017414517105/8893040219253127744:ℝ)],
  ![(252483382362435212788713/582814283808972979830784:ℝ), (754102761514100978435689/1748442851426918939492352:ℝ), (5865381956039456578213/13659709776772804214784:ℝ), (60827517388033368253/142288643508050043904:ℝ)],
  ![(124156611415134180851073/291407141904486489915392:ℝ), (370824188861875024288769/874221425713459469746176:ℝ), (2884259256761614244573/6829854888386402107392:ℝ), (29911525248717231413/71144321754025021952:ℝ)]]
theorem w8_monotone_lower (i : Fin 3) (j : Fin 4) :
    w8_monotone_minimum ≤ w8_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w8_monotone_minimum,w8_monotone_table]
theorem w8_monotone_identity (δ p : ℝ) :
    w8_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w8_monotone_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w8_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w8_monotone_table,Fin.sum_univ_succ]
  ring
theorem w8_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w8_monotone_power δ p := by
  rw [w8_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w8_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w8_monotone_lower
theorem w8_monotone_binding (δ p : ℝ) :
    w8_monotone_power δ p=guardMonotone Plane.C δ p := by
  norm_num [w8_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window8_admissible (δ p : ℝ) (ha : window8.Available δ p) :
    Admissible window8.plane δ p := by
  have hd : δ ∈ Set.Icc (15/32:ℝ) (123/256) := ha.1
  have hp : p ∈ Set.Icc (63/128:ℝ) (1/2) := ha.2
  change Admissible Plane.C δ p
  constructor
  · rw [←w8_dn_binding]
    exact w8_dn_positive hd hp
  · rw [←w8_aa_binding]
    exact w8_aa_positive hd hp
  · rw [←w8_cc_binding]
    exact w8_cc_positive hd hp
  · rw [←w8_j_binding]
    exact w8_j_positive hd hp
  · rw [←w8_tlo_binding]
    exact w8_tlo_positive hd hp
  · rw [←w8_thi_binding]
    exact w8_thi_positive hd hp
  · rw [←w8_rlo_binding]
    exact w8_rlo_positive hd hp
  · rw [←w8_rhi_binding]
    exact w8_rhi_positive hd hp
  · rw [←w8_mlo_binding]
    exact w8_mlo_positive hd hp
  · rw [←w8_mhi_binding]
    exact w8_mhi_positive hd hp
  · rw [←w8_widthlo_binding]
    exact w8_widthlo_positive hd hp
  · rw [←w8_tail_binding]
    exact w8_tail_positive hd hp
  · rw [←w8_monotone_binding]
    exact w8_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window8_admissible
