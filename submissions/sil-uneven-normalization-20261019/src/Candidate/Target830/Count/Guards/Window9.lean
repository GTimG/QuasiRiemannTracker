import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w9_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-772765011/372765011)*δ^0*p^1
def w9_dn_minimum : ℝ := 1463825055/745530022
def w9_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)]]
theorem w9_dn_lower (i : Fin 3) (j : Fin 4) :
    w9_dn_minimum ≤ w9_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_dn_minimum,w9_dn_table]
theorem w9_dn_identity (δ p : ℝ) :
    w9_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_dn_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_dn_table,Fin.sum_univ_succ]
  ring
theorem w9_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_dn_power δ p := by
  rw [w9_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_dn_lower
theorem w9_dn_binding (δ p : ℝ) :
    w9_dn_power δ p=guardD Plane.C δ p := by
  norm_num [w9_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-400000000/372765011)*δ^0*p^1
def w9_aa_minimum : ℝ := 545530022/372765011
def w9_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)]]
theorem w9_aa_lower (i : Fin 3) (j : Fin 4) :
    w9_aa_minimum ≤ w9_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_aa_minimum,w9_aa_table]
theorem w9_aa_identity (δ p : ℝ) :
    w9_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_aa_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_aa_table,Fin.sum_univ_succ]
  ring
theorem w9_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_aa_power δ p := by
  rw [w9_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_aa_lower
theorem w9_aa_binding (δ p : ℝ) :
    w9_aa_power δ p=guardA Plane.C δ p := by
  norm_num [w9_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-195798850/372765011)*δ^0*p^1
def w9_cc_minimum : ℝ := 274865586/372765011
def w9_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)]]
theorem w9_cc_lower (i : Fin 3) (j : Fin 4) :
    w9_cc_minimum ≤ w9_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_cc_minimum,w9_cc_table]
theorem w9_cc_identity (δ p : ℝ) :
    w9_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_cc_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_cc_table,Fin.sum_univ_succ]
  ring
theorem w9_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_cc_power δ p := by
  rw [w9_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_cc_lower
theorem w9_cc_binding (δ p : ℝ) :
    w9_cc_power δ p=guardC Plane.C δ p := by
  norm_num [w9_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-1287941685/745530022)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (400000000/372765011)*δ^1*p^2
def w9_j_minimum : ℝ := 98288752121/95427842816
def w9_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(12919163924857/12214763880448:ℝ), (6432536065423/6107381940224:ℝ), (12811108461835/12214763880448:ℝ), (199332389341/190855685632:ℝ)],
  ![(25661942873411/24429527760896:ℝ), (12776890135189/12214763880448:ℝ), (25445877042345/24429527760896:ℝ), (395909893583/381711371264:ℝ)],
  ![(6371389474277/6107381940224:ℝ), (3172177034883/3053690970112:ℝ), (6317384290255/6107381940224:ℝ), (98288752121/95427842816:ℝ)]]
theorem w9_j_lower (i : Fin 3) (j : Fin 4) :
    w9_j_minimum ≤ w9_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_j_minimum,w9_j_table]
theorem w9_j_identity (δ p : ℝ) :
    w9_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_j_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_j_table,Fin.sum_univ_succ]
  ring
theorem w9_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_j_power δ p := by
  rw [w9_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_j_lower
theorem w9_j_binding (δ p : ℝ) :
    w9_j_power δ p=guardJ Plane.C δ p := by
  norm_num [w9_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-568563861/372765011)*δ^1*p^1 +
  (195798850/372765011)*δ^1*p^2
def w9_tlo_minimum : ℝ := 16904233539/95427842816
def w9_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(141425928947355/781744888348672:ℝ), (140439765805641/781744888348672:ℝ), (2179025258443/12214763880448:ℝ), (16904233539/95427842816:ℝ)],
  ![(286301270795865/1563489776697344:ℝ), (284304891752883/1563489776697344:ℝ), (4411197474409/24429527760896:ℝ), (34220765457/190855685632:ℝ)],
  ![(72437670924255/390872444174336:ℝ), (71932562973621/390872444174336:ℝ), (1116086107983/6107381940224:ℝ), (8658265959/47713921408:ℝ)]]
theorem w9_tlo_lower (i : Fin 3) (j : Fin 4) :
    w9_tlo_minimum ≤ w9_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_tlo_minimum,w9_tlo_table]
theorem w9_tlo_identity (δ p : ℝ) :
    w9_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_tlo_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_tlo_table,Fin.sum_univ_succ]
  ring
theorem w9_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_tlo_power δ p := by
  rw [w9_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_tlo_lower
theorem w9_tlo_binding (δ p : ℝ) :
    w9_tlo_power δ p=guardTLo Plane.C δ p := by
  norm_num [w9_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-643713254163/1491060044000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (4754098847511/3727650110000)*δ^1*p^1 +
  (-95838850/372765011)*δ^1*p^2
def w9_thi_minimum : ℝ := 18414864857213517/244295277608960000
def w9_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(40748757000773697/488590555217920000:ℝ), (40824407391410991/488590555217920000:ℝ), (2044941492339133/24429527760896000:ℝ), (160046970183159/1908556856320000:ℝ)],
  ![(77578486715200731/977181110435840000:ℝ), (77745030237146613/977181110435840000:ℝ), (3895454396946031/48859055521792000:ℝ), (304963514923917/3817113712640000:ℝ)],
  ![(18414864857213517/244295277608960000:ℝ), (18460311422867811/244295277608960000:ℝ), (925256452303449/12214763880448000:ℝ), (72458272370379/954278428160000:ℝ)]]
theorem w9_thi_lower (i : Fin 3) (j : Fin 4) :
    w9_thi_minimum ≤ w9_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_thi_minimum,w9_thi_table]
theorem w9_thi_identity (δ p : ℝ) :
    w9_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_thi_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_thi_table,Fin.sum_univ_succ]
  ring
theorem w9_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_thi_power δ p := by
  rw [w9_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_thi_lower
theorem w9_thi_binding (δ p : ℝ) :
    w9_thi_power δ p=guardTHi Plane.C δ p := by
  norm_num [w9_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-24310471945/27584610814)*δ^0*p^1 +
  (2301650128018533120/5141288876755714477)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-55163398065/13792305407)*δ^1*p^1 +
  (15893629311901003644/5141288876755714477)*δ^1*p^2 +
  (-4327484061600000000/5141288876755714477)*δ^1*p^3
def w9_rlo_minimum : ℝ := 697709252535174556215/2632339904898925812224
def w9_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1478762550493988625361889/5391032125233000063434752:ℝ), (118540409228431464270145/437110712856729734873088:ℝ), (135504443117513809521853/505409261740593755947008:ℝ), (697709252535174556215/2632339904898925812224:ℝ)],
  ![(2991946247753509739842747/10782064250466000126869504:ℝ), (8874479706558244375922855/32346192751398000380608512:ℝ), (274187715450137149311599/1010818523481187511894016:ℝ), (1411851235850802976845/5264679809797851624448:ℝ)],
  ![(20448428341344879925417/72851785476121622478848:ℝ), (2244242282553140098963745/8086548187849500095152128:ℝ), (1874098274765180267429/6829854888386402107392:ℝ), (357070991657814210315/1316169952449462906112:ℝ)]]
theorem w9_rlo_lower (i : Fin 3) (j : Fin 4) :
    w9_rlo_minimum ≤ w9_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_rlo_minimum,w9_rlo_table]
theorem w9_rlo_identity (δ p : ℝ) :
    w9_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_rlo_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_rlo_table,Fin.sum_univ_succ]
  ring
theorem w9_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_rlo_power δ p := by
  rw [w9_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_rlo_lower
theorem w9_rlo_binding (δ p : ℝ) :
    w9_rlo_power δ p=guardRLo Plane.C δ p := by
  norm_num [w9_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-2266935935/745530022)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (1360161561/372765011)*δ^1*p^1 +
  (-151306500474037350/138953753425830121)*δ^1*p^2
def w9_rhi_minimum : ℝ := 8784753705378582855/17786080438506255488
def w9_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(150936880583239022497343/291407141904486489915392:ℝ), (450740471721542711046271/874221425713459469746176:ℝ), (7010580245369371332617/13659709776772804214784:ℝ), (18173040108073251555/35572160877012510976:ℝ)],
  ![(296861097235669368970789/582814283808972979830784:ℝ), (886511702684805405858533/1748442851426918939492352:ℝ), (13788336792553043986291/27319419553545608429568:ℝ), (35742547518830417265/71144321754025021952:ℝ)],
  ![(72962108326215173236723/145703570952243244957696:ℝ), (217885615481631347406131/437110712856729734873088:ℝ), (3388878273591836326837/6829854888386402107392:ℝ), (8784753705378582855/17786080438506255488:ℝ)]]
theorem w9_rhi_lower (i : Fin 3) (j : Fin 4) :
    w9_rhi_minimum ≤ w9_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_rhi_minimum,w9_rhi_table]
theorem w9_rhi_identity (δ p : ℝ) :
    w9_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_rhi_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_rhi_table,Fin.sum_univ_succ]
  ring
theorem w9_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_rhi_power δ p := by
  rw [w9_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_rhi_lower
theorem w9_rhi_binding (δ p : ℝ) :
    w9_rhi_power δ p=guardRHi Plane.C δ p := by
  norm_num [w9_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_mlo_power (δ p : ℝ) : ℝ := (-612155921/1000000000)*δ^0*p^0 +
  (234921084425093377/186382505500000000)*δ^0*p^1 +
  (-80408245463812802801144049/138953753425830121000000000)*δ^0*p^2 +
  (3112155921/2500000000)*δ^1*p^0 +
  (-1218644907274906623/465956263750000000)*δ^1*p^1 +
  (1353886465924906623/931912527500000000)*δ^1*p^2 +
  (-576042239150560242/3473843835645753025)*δ^1*p^3
def w9_mlo_minimum : ℝ := 10575969500362800467939013621931/1457035709522432449576960000000000
def w9_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(10575969500362800467939013621931/1457035709522432449576960000000000:ℝ), (32449772107251928930773623686943/4371107128567297348730880000000000:ℝ), (259154596438255649764409501759/34149274441932010536960000000000:ℝ), (551656756989681461565505443/71144321754025021952000000000:ℝ)],
  ![(26099855056848852429076679525513/2914071419044864899153920000000000:ℝ), (79569108398395779730916241193669/8742214257134594697461760000000000:ℝ), (631564185651617200163485582117/68298548883864021073920000000000:ℝ), (1336467302912267556721900209/142288643508050043904000000000:ℝ)],
  ![(7761942778243025980568832951791/728517854761216224788480000000000:ℝ), (23559668145571925400071308753363/2185553564283648674365440000000000:ℝ), (186204794606680775199538040179/17074637220966005268480000000000:ℝ), (392405272961293047578197383/35572160877012510976000000000:ℝ)]]
theorem w9_mlo_lower (i : Fin 3) (j : Fin 4) :
    w9_mlo_minimum ≤ w9_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_mlo_minimum,w9_mlo_table]
theorem w9_mlo_identity (δ p : ℝ) :
    w9_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_mlo_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_mlo_table,Fin.sum_univ_succ]
  ring
theorem w9_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_mlo_power δ p := by
  rw [w9_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_mlo_lower
theorem w9_mlo_binding (δ p : ℝ) :
    w9_mlo_power δ p=guardMLo Plane.C δ p := by
  norm_num [w9_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-6287390142794251/4659562637500000)*δ^0*p^1 +
  (2116941220965473617000587/3473843835645753025000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (30373484644705749/11648906593750000)*δ^1*p^1 +
  (-32789348625955749/23297813187500000)*δ^1*p^2 +
  (101948830800770718/694768767129150605)*δ^1*p^3
def w9_mhi_minimum : ℝ := 5619534904979715031606371/889304021925312774400000000
def w9_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(779885302559566559998018889569/72851785476121622478848000000000:ℝ), (1138209064535611498075052544091/109277678214182433718272000000000:ℝ), (8645883348190826147676068683/853731861048300263424000000000:ℝ), (17500384760414062452228591/1778608043850625548800000000:ℝ)],
  ![(1294507380052615617620731388987/145703570952243244957696000000000:ℝ), (1882954167099008838110443683353/218555356428364867436544000000000:ℝ), (14252203340974716343458785129/1707463722096600526848000000000:ℝ), (28739454570373492515441333/3557216087701251097600000000:ℝ)],
  ![(257311038746524528811356249709/36425892738060811239424000000000:ℝ), (372372551281698670017695569631/54638839107091216859136000000000:ℝ), (2803159996391945097891358223/426865930524150131712000000000:ℝ), (5619534904979715031606371/889304021925312774400000000:ℝ)]]
theorem w9_mhi_lower (i : Fin 3) (j : Fin 4) :
    w9_mhi_minimum ≤ w9_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_mhi_minimum,w9_mhi_table]
theorem w9_mhi_identity (δ p : ℝ) :
    w9_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_mhi_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_mhi_table,Fin.sum_univ_succ]
  ring
theorem w9_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_mhi_power δ p := by
  rw [w9_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_mhi_lower
theorem w9_mhi_binding (δ p : ℝ) :
    w9_mhi_power δ p=guardMHi Plane.C δ p := by
  norm_num [w9_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_widthlo_power (δ p : ℝ) : ℝ := (5565906092767/8000000000000)*δ^0*p^0 +
  (-2051607364334019258479/1491060044000000000000)*δ^0*p^1 +
  (687632641159884323317578759423/1111630027406640968000000000000)*δ^0*p^2 +
  (-25565906092767/20000000000000)*δ^1*p^0 +
  (9710652314219380741521/3727650110000000000000)*δ^1*p^1 +
  (-10391389548559180741521/7455300220000000000000)*δ^1*p^2 +
  (979845789367848241521/6947687671291506050000)*δ^1*p^3
def w9_widthlo_minimum : ℝ := 3274422554171256732873538483959/284577287016100087808000000000000
def w9_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(187383180181079680800892310272113463/11656285676179459596615680000000000000:ℝ), (550733020763725470688385438158221839/34968857028538378789847040000000000000:ℝ), (4213682206227271185405597359103407/273194195535456084295680000000000000:ℝ), (8593840744271006353080623472339/569154574032200175616000000000000:ℝ)],
  ![(331469547425130251038083280213999949/23312571352358919193231360000000000000:ℝ), (973000780318582996281226746155362837/69937714057076757579694080000000000000:ℝ), (7434786536816193588092358104919541/546388391070912168591360000000000000:ℝ), (15142685852613519818827700440257/1138309148064400351232000000000000:ℝ)],
  ![(72043183622025285118595484970943243/5828142838089729798307840000000000000:ℝ), (211133879777428762796420653998570499/17484428514269189394923520000000000000:ℝ), (1610552165294461201343380372908067/136597097767728042147840000000000000:ℝ), (3274422554171256732873538483959/284577287016100087808000000000000:ℝ)]]
theorem w9_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w9_widthlo_minimum ≤ w9_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_widthlo_minimum,w9_widthlo_table]
theorem w9_widthlo_identity (δ p : ℝ) :
    w9_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_widthlo_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w9_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_widthlo_power δ p := by
  rw [w9_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_widthlo_lower
theorem w9_widthlo_binding (δ p : ℝ) :
    w9_widthlo_power δ p=guardWidth Plane.C δ p := by
  norm_num [w9_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-3899358951306417/4659562637500000)*δ^1*p^1 +
  (35812707313/111829503300)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (18756998265080749/11648906593750000)*δ^2*p^1 +
  (-70580026487/93191252750)*δ^2*p^2 +
  (27200000/372765011)*δ^2*p^3
def w9_tail_minimum : ℝ := 615587010772624443/381711371264000000000
def w9_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(4890571984589874833041/1563489776697344000000000:ℝ), (4732721144319340976323/1563489776697344000000000:ℝ), (171562289689876418743/58630866626150400000000:ℝ), (4313871372142498563/1526845485056000000000:ℝ)],
  ![(1970416610068622371261/781744888348672000000000:ℝ), (1895788204333633238023/781744888348672000000000:ℝ), (68294756691783895531/29315433313075200000000:ℝ), (1705702113951000903/763422742528000000000:ℝ)],
  ![(735464103113642428281/390872444174336000000000:ℝ), (700426688410283798523/390872444174336000000000:ℝ), (8317390694034576133/4885905552179200000000:ℝ), (615587010772624443/381711371264000000000:ℝ)]]
theorem w9_tail_lower (i : Fin 3) (j : Fin 4) :
    w9_tail_minimum ≤ w9_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_tail_minimum,w9_tail_table]
theorem w9_tail_identity (δ p : ℝ) :
    w9_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_tail_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_tail_table,Fin.sum_univ_succ]
  ring
theorem w9_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_tail_power δ p := by
  rw [w9_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_tail_lower
theorem w9_tail_binding (δ p : ℝ) :
    w9_tail_power δ p=guardTail Plane.C δ p := by
  norm_num [w9_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w9_monotone_power (δ p : ℝ) : ℝ := (777438810/372765011)*δ^0*p^0 +
  (-978994250/372765011)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-941328872/372765011)*δ^1*p^0 +
  (1191597700/372765011)*δ^1*p^1 +
  (-154438583925962650/138953753425830121)*δ^1*p^2
def w9_monotone_minimum : ℝ := 14453529179059162993/35572160877012510976
def w9_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(124156611415134180851073/291407141904486489915392:ℝ), (370824188861875024288769/874221425713459469746176:ℝ), (2884259256761614244573/6829854888386402107392:ℝ), (29911525248717231413/71144321754025021952:ℝ)],
  ![(244143063298101510615579/582814283808972979830784:ℝ), (729193993933399118719387/1748442851426918939492352:ℝ), (5671655071007000400079/13659709776772804214784:ℝ), (58818583606835557399/142288643508050043904:ℝ)],
  ![(59993225941483664882253/145703570952243244957696:ℝ), (179184902535762047215309/437110712856729734873088:ℝ), (1393697907122693077753/3414927444193201053696:ℝ), (14453529179059162993/35572160877012510976:ℝ)]]
theorem w9_monotone_lower (i : Fin 3) (j : Fin 4) :
    w9_monotone_minimum ≤ w9_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w9_monotone_minimum,w9_monotone_table]
theorem w9_monotone_identity (δ p : ℝ) :
    w9_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w9_monotone_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w9_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w9_monotone_table,Fin.sum_univ_succ]
  ring
theorem w9_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w9_monotone_power δ p := by
  rw [w9_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w9_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w9_monotone_lower
theorem w9_monotone_binding (δ p : ℝ) :
    w9_monotone_power δ p=guardMonotone Plane.C δ p := by
  norm_num [w9_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window9_admissible (δ p : ℝ) (ha : window9.Available δ p) :
    Admissible window9.plane δ p := by
  have hd : δ ∈ Set.Icc (123/256:ℝ) (63/128) := ha.1
  have hp : p ∈ Set.Icc (63/128:ℝ) (1/2) := ha.2
  change Admissible Plane.C δ p
  constructor
  · rw [←w9_dn_binding]
    exact w9_dn_positive hd hp
  · rw [←w9_aa_binding]
    exact w9_aa_positive hd hp
  · rw [←w9_cc_binding]
    exact w9_cc_positive hd hp
  · rw [←w9_j_binding]
    exact w9_j_positive hd hp
  · rw [←w9_tlo_binding]
    exact w9_tlo_positive hd hp
  · rw [←w9_thi_binding]
    exact w9_thi_positive hd hp
  · rw [←w9_rlo_binding]
    exact w9_rlo_positive hd hp
  · rw [←w9_rhi_binding]
    exact w9_rhi_positive hd hp
  · rw [←w9_mlo_binding]
    exact w9_mlo_positive hd hp
  · rw [←w9_mhi_binding]
    exact w9_mhi_positive hd hp
  · rw [←w9_widthlo_binding]
    exact w9_widthlo_positive hd hp
  · rw [←w9_tail_binding]
    exact w9_tail_positive hd hp
  · rw [←w9_monotone_binding]
    exact w9_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window9_admissible
