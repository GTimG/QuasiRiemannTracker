import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w5_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-77961251/37961251)*δ^0*p^1
def w5_dn_minimum : ℝ := 149806255/75922502
def w5_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(19253161891/9718080256:ℝ), (28840762211/14577120384:ℝ), (57603563171/29154240768:ℝ), (149806255/75922502:ℝ)],
  ![(19253161891/9718080256:ℝ), (28840762211/14577120384:ℝ), (57603563171/29154240768:ℝ), (149806255/75922502:ℝ)],
  ![(19253161891/9718080256:ℝ), (28840762211/14577120384:ℝ), (57603563171/29154240768:ℝ), (149806255/75922502:ℝ)]]
theorem w5_dn_lower (i : Fin 3) (j : Fin 4) :
    w5_dn_minimum ≤ w5_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_dn_minimum,w5_dn_table]
theorem w5_dn_identity (δ p : ℝ) :
    w5_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_dn_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_dn_table,Fin.sum_univ_succ]
  ring
theorem w5_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_dn_power δ p := by
  rw [w5_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_dn_lower
theorem w5_dn_binding (δ p : ℝ) :
    w5_dn_power δ p=guardD Plane.A δ p := by
  norm_num [w5_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-40000000/37961251)*δ^0*p^1
def w5_aa_minimum : ℝ := 55922502/37961251
def w5_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(56078752/37961251:ℝ), (168080006/113883753:ℝ), (167923756/113883753:ℝ), (55922502/37961251:ℝ)],
  ![(56078752/37961251:ℝ), (168080006/113883753:ℝ), (167923756/113883753:ℝ), (55922502/37961251:ℝ)],
  ![(56078752/37961251:ℝ), (168080006/113883753:ℝ), (167923756/113883753:ℝ), (55922502/37961251:ℝ)]]
theorem w5_aa_lower (i : Fin 3) (j : Fin 4) :
    w5_aa_minimum ≤ w5_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_aa_minimum,w5_aa_table]
theorem w5_aa_identity (δ p : ℝ) :
    w5_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_aa_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_aa_table,Fin.sum_univ_succ]
  ring
theorem w5_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_aa_power δ p := by
  rw [w5_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_aa_lower
theorem w5_aa_binding (δ p : ℝ) :
    w5_aa_power δ p=guardA Plane.A δ p := by
  norm_num [w5_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-19632294/37961251)*δ^0*p^1
def w5_cc_minimum : ℝ := 28145104/37961251
def w5_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3612389459/4859040128:ℝ), (1804558705/2429520064:ℝ), (3605845361/4859040128:ℝ), (28145104/37961251:ℝ)],
  ![(3612389459/4859040128:ℝ), (1804558705/2429520064:ℝ), (3605845361/4859040128:ℝ), (28145104/37961251:ℝ)],
  ![(3612389459/4859040128:ℝ), (1804558705/2429520064:ℝ), (3605845361/4859040128:ℝ), (28145104/37961251:ℝ)]]
theorem w5_cc_lower (i : Fin 3) (j : Fin 4) :
    w5_cc_minimum ≤ w5_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_cc_minimum,w5_cc_table]
theorem w5_cc_identity (δ p : ℝ) :
    w5_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_cc_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_cc_table,Fin.sum_univ_succ]
  ring
theorem w5_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_cc_power δ p := by
  rw [w5_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_cc_lower
theorem w5_cc_binding (δ p : ℝ) :
    w5_cc_power δ p=guardC Plane.A δ p := by
  norm_num [w5_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-389806255/227767506)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (40000000/37961251)*δ^1*p^2
def w5_j_minimum : ℝ := 62922805897/58308481536
def w5_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(32521585419175/29853942546432:ℝ), (3042736986635/2798807113728:ℝ), (97170628855865/89561827639296:ℝ), (252536177365/233233926144:ℝ)],
  ![(64934999812403/59707885092864:ℝ), (6075333425095/5597614227456:ℝ), (194016777112621/179123655278592:ℝ), (504227400953/466467852288:ℝ)],
  ![(8103353598307/7463485636608:ℝ), (758149109615/699701778432:ℝ), (24211537064189/22390456909824:ℝ), (62922805897/58308481536:ℝ)]]
theorem w5_j_lower (i : Fin 3) (j : Fin 4) :
    w5_j_minimum ≤ w5_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_j_minimum,w5_j_table]
theorem w5_j_identity (δ p : ℝ) :
    w5_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_j_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_j_table,Fin.sum_univ_succ]
  ring
theorem w5_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_j_power δ p := by
  rw [w5_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_j_lower
theorem w5_j_binding (δ p : ℝ) :
    w5_j_power δ p=guardJ Plane.A δ p := by
  norm_num [w5_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-57593545/37961251)*δ^1*p^1 +
  (19632294/37961251)*δ^1*p^2
def w5_tlo_minimum : ℝ := 817967085/4859040128
def w5_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(216689181698115/1273768215314432:ℝ), (215932987472705/1273768215314432:ℝ), (1681080583985/9951314182144:ℝ), (817967085/4859040128:ℝ)],
  ![(434776358116863/2547536430628864:ℝ), (433259090993621/2547536430628864:ℝ), (3373006849157/19902628364288:ℝ), (1641211377/9718080256:ℝ)],
  ![(54521794104687/318442053828608:ℝ), (54331525880229/318442053828608:ℝ), (422981566293/2487828545536:ℝ), (205811073/1214760032:ℝ)]]
theorem w5_tlo_lower (i : Fin 3) (j : Fin 4) :
    w5_tlo_minimum ≤ w5_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_tlo_minimum,w5_tlo_table]
theorem w5_tlo_identity (δ p : ℝ) :
    w5_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_tlo_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_tlo_table,Fin.sum_univ_succ]
  ring
theorem w5_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_tlo_power δ p := by
  rw [w5_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_tlo_lower
theorem w5_tlo_binding (δ p : ℝ) :
    w5_tlo_power δ p=guardTLo Plane.A δ p := by
  norm_num [w5_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-64941722083/151845004000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (481070283751/379612510000)*δ^1*p^1 +
  (-9636294/37961251)*δ^1*p^2
def w5_thi_minimum : ℝ := 19924627063688473/199026283642880000
def w5_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3251724266882413/31844205382860800:ℝ), (48796645082923721/477663080742912000:ℝ), (6102143263477109/59707885092864000:ℝ), (15897580429009/155489284096000:ℝ)],
  ![(160991614926814217/1592210269143040000:ℝ), (96638381324323837/955326161485824000:ℝ), (60425769860103293/597078850928640000:ℝ), (157427604673849/1554892840960000:ℝ)],
  ![(19924627063688473/199026283642880000:ℝ), (11960434060350029/119415770185728000:ℝ), (7478763385679437/74634856366080000:ℝ), (19484925632201/194361605120000:ℝ)]]
theorem w5_thi_lower (i : Fin 3) (j : Fin 4) :
    w5_thi_minimum ≤ w5_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_thi_minimum,w5_thi_table]
theorem w5_thi_identity (δ p : ℝ) :
    w5_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_thi_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_thi_table,Fin.sum_univ_succ]
  ring
theorem w5_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_thi_power δ p := by
  rw [w5_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_thi_lower
theorem w5_thi_binding (δ p : ℝ) :
    w5_thi_power δ p=guardTHi Plane.A δ p := by
  norm_num [w5_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-7424970815/8427397722)*δ^0*p^1 +
  (71151849489794090/159957280100835111)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-5566665949/1404566287)*δ^1*p^1 +
  (161838647733662392/53319093366945037)*δ^1*p^2 +
  (-43658300560000000/53319093366945037)*δ^1*p^3
def w5_rlo_minimum : ℝ := 27692112367383628975/109197503215503435776
def w5_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(692527090894141179860365/2683637839024212437630976:ℝ), (344260599837316895170055/1341818919512106218815488:ℝ), (32087467517913871219085/125795523704259958013952:ℝ), (27692112367383628975/109197503215503435776:ℝ)],
  ![(1389345023352359898680849/5367275678048424875261952:ℝ), (690658654624040213379091/2683637839024212437630976:ℝ), (64374578045858743486993/251591047408519916027904:ℝ), (55556883594057115355/218395006431006871552:ℝ)],
  ![(4708229273366342694733/18132688101514948902912:ℝ), (86599513696680829552259/335454729878026554703872:ℝ), (8071777631986218066977/31448880926064989503488:ℝ), (6966192806668371595/27299375803875858944:ℝ)]]
theorem w5_rlo_lower (i : Fin 3) (j : Fin 4) :
    w5_rlo_minimum ≤ w5_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_rlo_minimum,w5_rlo_table]
theorem w5_rlo_identity (δ p : ℝ) :
    w5_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_rlo_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_rlo_table,Fin.sum_univ_succ]
  ring
theorem w5_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_rlo_power δ p := by
  rw [w5_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_rlo_lower
theorem w5_rlo_binding (δ p : ℝ) :
    w5_rlo_power δ p=guardRLo Plane.A δ p := by
  norm_num [w5_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-684290665/227767506)*δ^0*p^1 +
  (1275465166866495/1441056577485001)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (136858133/37961251)*δ^1*p^1 +
  (-1530558200239794/1441056577485001)*δ^1*p^2
def w5_rhi_minimum : ℝ := 76157146822035955/138341431438560096
def w5_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(81025655713601276618885/145061504812119591223296:ℝ), (242528696857815270984965/435184514436358773669888:ℝ), (1890479047851393373385/3399879019034052919296:ℝ), (307000263140733175/553365725754240384:ℝ)],
  ![(161425362155595333075049/290123009624239182446592:ℝ), (483183781465226818846441/870369028872717547339776:ℝ), (3766353536534836068349/6799758038068105838592:ℝ), (611628850428876995/1106731451508480768:ℝ)],
  ![(20099926610498514114041/36265376203029897805824:ℝ), (60163771151852886965369/108796128609089693417472:ℝ), (468968622170860673741/849969754758513229824:ℝ), (76157146822035955/138341431438560096:ℝ)]]
theorem w5_rhi_lower (i : Fin 3) (j : Fin 4) :
    w5_rhi_minimum ≤ w5_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_rhi_minimum,w5_rhi_table]
theorem w5_rhi_identity (δ p : ℝ) :
    w5_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_rhi_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_rhi_table,Fin.sum_univ_succ]
  ring
theorem w5_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_rhi_power δ p := by
  rw [w5_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_rhi_lower
theorem w5_rhi_binding (δ p : ℝ) :
    w5_rhi_power δ p=guardRHi Plane.A δ p := by
  norm_num [w5_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_mlo_power (δ p : ℝ) : ℝ := (-955799/1562500)*δ^0*p^0 +
  (55875190723837/44485841015625)*δ^0*p^1 +
  (-3871698059836068563183/6754952706960942187500)*δ^0*p^2 +
  (4862049/3906250)*δ^1*p^0 +
  (-193319710923692/74143068359375)*δ^1*p^1 +
  (213769647876817/148286136718750)*δ^1*p^2 +
  (-5918233622460002/36026414437125025)*δ^1*p^3
def w5_mlo_minimum : ℝ := 477843514905029042987183711/2901230096242391824465920000000
def w5_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(477843514905029042987183711/2901230096242391824465920000000:ℝ), (66182951278993832486614321/226658601268936861286400000000:ℝ), (278321216434907527991237/664038870905088460800000000:ℝ), (503672642373223899397/922276209590400640000000:ℝ)],
  ![(84645972701336493888612482899/145061504812119591223296000000000:ℝ), (1605494662417545987396528793/2266586012689368612864000000000:ℝ), (5531471259929085156301517/6640388709050884608000000000:ℝ), (8831078270737885375117/9222762095904006400000000:ℝ)],
  ![(18174971207177691953483222531/18132688101514948902912000000000:ℝ), (318644976505644206240864297/283323251586171076608000000000:ℝ), (1034966294438636879086333/830048588631360576000000000:ℝ), (1578178764717941469533/1152845261988000800000000:ℝ)]]
theorem w5_mlo_lower (i : Fin 3) (j : Fin 4) :
    w5_mlo_minimum ≤ w5_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_mlo_minimum,w5_mlo_table]
theorem w5_mlo_identity (δ p : ℝ) :
    w5_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_mlo_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_mlo_table,Fin.sum_univ_succ]
  ring
theorem w5_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_mlo_power δ p := by
  rw [w5_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_mlo_lower
theorem w5_mlo_binding (δ p : ℝ) :
    w5_mlo_power δ p=guardMLo Plane.A δ p := by
  norm_num [w5_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-1914282981896273/1423546912500000)*δ^0*p^1 +
  (65228736770189796355841/108079243311375075000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (3083417861867909/1186289093750000)*δ^1*p^1 +
  (-3313432513117909/2372578187500000)*δ^1*p^2 +
  (5244756935881394/36026414437125025)*δ^1*p^3
def w5_mhi_minimum : ℝ := 314038744229834398330209/18445524191808012800000000
def w5_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(53612225925640532511750750133/2901230096242391824465920000000:ℝ), (22108585981189960286375196511/1208845873434329926860800000000:ℝ), (769189253205526459872463879/42498487737925661491200000000:ℝ), (264284145861286270704681/14756419353446410240000000:ℝ)],
  ![(2615359734049807090920105739697/145061504812119591223296000000000:ℝ), (215678689092678617593183059063/12088458734343299268608000000000:ℝ), (7502863791107799320039692639/424984877379256614912000000000:ℝ), (2577575706225768946844241/147564193534464102400000000:ℝ)],
  ![(318763521477198444531584246593/18132688101514948902912000000000:ℝ), (26283939796682204040326769127/1511057341792912408576000000000:ℝ), (914229381270041755169343311/53123109672407076864000000000:ℝ), (314038744229834398330209/18445524191808012800000000:ℝ)]]
theorem w5_mhi_lower (i : Fin 3) (j : Fin 4) :
    w5_mhi_minimum ≤ w5_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_mhi_minimum,w5_mhi_table]
theorem w5_mhi_identity (δ p : ℝ) :
    w5_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_mhi_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_mhi_table,Fin.sum_univ_succ]
  ring
theorem w5_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_mhi_power δ p := by
  rw [w5_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_mhi_lower
theorem w5_mhi_binding (δ p : ℝ) :
    w5_mhi_power δ p=guardMHi Plane.A δ p := by
  norm_num [w5_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_widthlo_power (δ p : ℝ) : ℝ := (557465456047/800000000000)*δ^0*p^0 +
  (-62525073342709634797/45553501200000000000)*δ^0*p^1 +
  (2120271664476671286175750349/3458535785964002400000000000)*δ^0*p^2 +
  (-2557465456047/2000000000000)*δ^1*p^0 +
  (98571993340036788401/37961251000000000000)*δ^1*p^1 +
  (-104956578977216788401/75922502000000000000)*δ^1*p^2 +
  (10066841231086488401/72052828874250050000)*δ^1*p^3
def w5_widthlo_minimum : ℝ := 40368718813528517241251999303/1770770322413569228800000000000
def w5_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(188228363718246053084161465985851/7736613589979711531909120000000000:ℝ), (8397216549170999158165680463944811/348147611549087018935910400000000000:ℝ), (10838929554054012692107254171577/453317202537873722572800000000000:ℝ), (33575527868256021768941851327/1416616257930855383040000000000:ℝ)],
  ![(9233650301800318030069902247532159/386830679498985576595456000000000000:ℝ), (82381074203783515924657736383012963/3481476115490870189359104000000000000:ℝ), (106329006368967653935727415951457/4533172025378737225728000000000000:ℝ), (329352514595394177809717253847/14166162579308553830400000000000:ℝ)],
  ![(1131985302211041675741466399471471/48353834937373197074432000000000000:ℝ), (10098747864482130033457333515822227/435184514436358773669888000000000000:ℝ), (13033589649674397618797786273393/566646503172342153216000000000000:ℝ), (40368718813528517241251999303/1770770322413569228800000000000:ℝ)]]
theorem w5_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w5_widthlo_minimum ≤ w5_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_widthlo_minimum,w5_widthlo_table]
theorem w5_widthlo_identity (δ p : ℝ) :
    w5_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_widthlo_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w5_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_widthlo_power δ p := by
  rw [w5_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_widthlo_lower
theorem w5_widthlo_binding (δ p : ℝ) :
    w5_widthlo_power δ p=guardWidth Plane.A δ p := by
  norm_num [w5_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-1185206091757091/1423546912500000)*δ^1*p^1 +
  (3582732233/11388375300)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (1900553477242909/1186289093750000)*δ^2*p^1 +
  (-7082745647/9490312750)*δ^2*p^2 +
  (2720000/37961251)*δ^2*p^3
def w5_tail_minimum : ℝ := 792591448648813203/155489284096000000000
def w5_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(452328417041653165499/81521165780123648000000:ℝ), (2236300069792617353611/407605828900618240000000:ℝ), (207279446268340111283/38213046459432960000000:ℝ), (533614383638814083/99513141821440000000:ℝ)],
  ![(2759169471068714654767/509507286125772800000000:ℝ), (2727793343403337888627/509507286125772800000000:ℝ), (252791680019873247323/47766308074291200000000:ℝ), (650664954369787307/124391427276800000000:ℝ)],
  ![(3362865941147117285751/636884107657216000000000:ℝ), (664805806075900108191/127376821531443200000000:ℝ), (102663282869895318337/19902628364288000000000:ℝ), (792591448648813203/155489284096000000000:ℝ)]]
theorem w5_tail_lower (i : Fin 3) (j : Fin 4) :
    w5_tail_minimum ≤ w5_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_tail_minimum,w5_tail_table]
theorem w5_tail_identity (δ p : ℝ) :
    w5_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_tail_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_tail_table,Fin.sum_univ_succ]
  ring
theorem w5_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_tail_power δ p := by
  rw [w5_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_tail_lower
theorem w5_tail_binding (δ p : ℝ) :
    w5_tail_power δ p=guardTail Plane.A δ p := by
  norm_num [w5_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w5_monotone_power (δ p : ℝ) : ℝ := (237048460/113883753)*δ^0*p^0 +
  (-98161470/37961251)*δ^0*p^1 +
  (1275465166866495/1441056577485001)*δ^0*p^2 +
  (-95554796/37961251)*δ^1*p^0 +
  (119264588/37961251)*δ^1*p^1 +
  (-1558475359760206/1441056577485001)*δ^1*p^2
def w5_monotone_minimum : ℝ := 1004463478891479083/2213462903016961536
def w5_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(66780037581038906713595/145061504812119591223296:ℝ), (66634928508221115371945/145061504812119591223296:ℝ), (259726992687685997765/566646503172342153216:ℝ), (4049412990754297295/8853851612067846144:ℝ)],
  ![(133039584021896232080407/290123009624239182446592:ℝ), (132750510631405404920413/290123009624239182446592:ℝ), (517429751126914534825/1133293006344684306432:ℝ), (8067266906320213627/17707703224135692288:ℝ)],
  ![(16564886610214331341703/36265376203029897805824:ℝ), (16528895530796072387117/36265376203029897805824:ℝ), (64425689609807134265/141661625793085538304:ℝ), (1004463478891479083/2213462903016961536:ℝ)]]
theorem w5_monotone_lower (i : Fin 3) (j : Fin 4) :
    w5_monotone_minimum ≤ w5_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w5_monotone_minimum,w5_monotone_table]
theorem w5_monotone_identity (δ p : ℝ) :
    w5_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w5_monotone_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w5_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w5_monotone_table,Fin.sum_univ_succ]
  ring
theorem w5_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w5_monotone_power δ p := by
  rw [w5_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w5_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w5_monotone_lower
theorem w5_monotone_binding (δ p : ℝ) :
    w5_monotone_power δ p=guardMonotone Plane.A δ p := by
  norm_num [w5_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window5_admissible (δ p : ℝ) (ha : window5.Available δ p) :
    Admissible window5.plane δ p := by
  have hd : δ ∈ Set.Icc (465/1024:ℝ) (117/256) := ha.1
  have hp : p ∈ Set.Icc (127/256:ℝ) (1/2) := ha.2
  change Admissible Plane.A δ p
  constructor
  · rw [←w5_dn_binding]
    exact w5_dn_positive hd hp
  · rw [←w5_aa_binding]
    exact w5_aa_positive hd hp
  · rw [←w5_cc_binding]
    exact w5_cc_positive hd hp
  · rw [←w5_j_binding]
    exact w5_j_positive hd hp
  · rw [←w5_tlo_binding]
    exact w5_tlo_positive hd hp
  · rw [←w5_thi_binding]
    exact w5_thi_positive hd hp
  · rw [←w5_rlo_binding]
    exact w5_rlo_positive hd hp
  · rw [←w5_rhi_binding]
    exact w5_rhi_positive hd hp
  · rw [←w5_mlo_binding]
    exact w5_mlo_positive hd hp
  · rw [←w5_mhi_binding]
    exact w5_mhi_positive hd hp
  · rw [←w5_widthlo_binding]
    exact w5_widthlo_positive hd hp
  · rw [←w5_tail_binding]
    exact w5_tail_positive hd hp
  · rw [←w5_monotone_binding]
    exact w5_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window5_admissible
