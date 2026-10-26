/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission20_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(391013200118207/3198839752287:ℝ), (383814360365920/3198839752287:ℝ)]]
theorem admission20_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission20_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission20_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_00_coefficients]
def admission20_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(285451488292736/3198839752287:ℝ), (281451488292736/3198839752287:ℝ)]]
theorem admission20_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission20_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission20_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_01_coefficients]
def admission20_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(144952152528932/3198839752287:ℝ), (143023972154176/3198839752287:ℝ)]]
theorem admission20_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission20_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission20_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_02_coefficients]
def admission20_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(42431489039009394944/28789557770583:ℝ), (9305543692024731904/3198839752287:ℝ), (41321212189213192192/28789557770583:ℝ)],
![(41870525930634181760/28789557770583:ℝ), (9180979772008614016/3198839752287:ℝ), (40761136017443344384/28789557770583:ℝ)]]
theorem admission20_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9951449223008629/19653671438051328:ℝ) admission20_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission20_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_03_coefficients]
def admission20_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(248687761049903656/1066279917429:ℝ), (486629518024708864/1066279917429:ℝ), (237991889664548864/1066279917429:ℝ)],
![(254927243751370996/1066279917429:ℝ), (1496912142433888384/3198839752287:ℝ), (732282737429381120/3198839752287:ℝ)]]
theorem admission20_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (29051744343817/363956878482432:ℝ) admission20_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission20_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_04_coefficients]
def admission20_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(92108068819906313342/666424948393125:ℝ), (332088306337645520876/1199564907107625:ℝ), (831333107429262719302/5997824535538125:ℝ)],
![(84963376372624277354/666424948393125:ℝ), (1532656321741122006484/5997824535538125:ℝ), (767848388419492777798/5997824535538125:ℝ)]]
theorem admission20_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (42481688186312138677/931729608915025920000:ℝ) admission20_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission20_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_05_coefficients]
def admission20_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(151113019794152608783820087350928896/3407447728350247988736212877:ℝ), (147548307401323431862898151683121664/1135815909450082662912070959:ℝ), (432055428885120582071470471279968256/3407447728350247988736212877:ℝ), (140523243474514553360052103581532160/3407447728350247988736212877:ℝ)],
![(154538695789159875104497342201846528/3407447728350247988736212877:ℝ), (150945224213891131641453218394310912/1135815909450082662912070959:ℝ), (442160798177324919703469049948356608/3407447728350247988736212877:ℝ), (143863534695807822824414736967270400/3407447728350247988736212877:ℝ)]]
theorem admission20_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (67006704079873348884607364455/581537745638442323410980331008:ℝ) admission20_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission20_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_06_coefficients]
def admission20_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(66500085764803471053980456216888/92093181847303999695573321:ℝ), (130938386995533141388803593681152/92093181847303999695573321:ℝ), (64446324253094804008510880174080/92093181847303999695573321:ℝ)],
![(64491899221310502794442004976444/92093181847303999695573321:ℝ), (126954117819977419759817376094336/92093181847303999695573321:ℝ), (62470116695078268280822301224960/92093181847303999695573321:ℝ)]]
theorem admission20_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (15251493333759342841997632135/62868945474426197125511387136:ℝ) admission20_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission20_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_07_coefficients]
def admission20_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(147966870069881065592928812757632348952182967823/177648884736311727807818906250000000000000:ℝ), (4312414335468919520812414116346726258979224477561/1598839962626805550270370156250000000000000:ℝ), (41662830815870864071134053592250905817437531719363/14389559663641249952433331406250000000000000:ℝ), (14836195995991612075387466750369777221688831814977/14389559663641249952433331406250000000000000:ℝ)],
![(6226991113905891039388519878301903741769154409/4441222118407793195195472656250000000000:ℝ), (140182688245908796147848262731913903800830660309/31976799252536111005407403125000000000000:ℝ), (65635774296979771500722355807288727595929605671747/14389559663641249952433331406250000000000000:ℝ), (22728790669360155751867065103854149395106618817857/14389559663641249952433331406250000000000000:ℝ)]]
theorem admission20_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (147966870069881065592928812757632348952182967823/63583012509444371216319664619520000000000000000000:ℝ) admission20_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission20_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_08_coefficients]
def admission20_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(11434676580783154066296536157695241783023/2997824929925260406756944042968750:ℝ), (11048205371815939651327750409776934825333/999274976641753468918981347656250:ℝ), (15995056255073218047519317483116432143808/1498912464962630203378472021484375:ℝ), (1028021147501964930770827076373089534464/299782492992526040675694404296875:ℝ)],
![(19121019867437678154929877463208767983703/5995649859850520813513888085937500:ℝ), (18390943164678461270663365537433683018093/1998549953283506937837962695312500:ℝ), (13247860488568572854225738095415126274784/1498912464962630203378472021484375:ℝ), (846985515695998993028228608630403388928/299782492992526040675694404296875:ℝ)]]
theorem admission20_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1654268585343748033258259001231256619/209563151581420657085037957120000000000:ℝ) admission20_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission20_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_09_coefficients]
def admission20_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83828580477446479846556790272/468580041838916015625:ℝ), (241454669863080455703643724032/468580041838916015625:ℝ), (231454103711694352351917077248/468580041838916015625:ℝ), (73828256735435376494830143488/468580041838916015625:ℝ)],
![(153006769873339616712524727808/468580041838916015625:ℝ), (263621448363559197497712877312/281148025103349609375:ℝ), (1259327424579205509789306222848/1405740125516748046875:ℝ), (44471329498283708048701779968/156193347279638671875:ℝ)],
![(13793365021681195660118154112/93716008367783203125:ℝ), (591861704318327434820909358272/1405740125516748046875:ℝ), (563104203698374688185726781504/1405740125516748046875:ℝ), (59381240233265479422196578304/468580041838916015625:ℝ)]]
theorem admission20_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (28994746207649159874119423/13975944133725388800000000000:ℝ) admission20_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission20_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_10_coefficients]
def admission20_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(54594078083930113315139405384648/92093181847303999695573321:ℝ), (107503015782217639655068407337984/92093181847303999695573321:ℝ), (52916638166433656307183510691840/92093181847303999695573321:ℝ)],
![(52907185560282105477252052805444/92093181847303999695573321:ℝ), (104156660456613650259284116429312/92093181847303999695573321:ℝ), (51257046303213392343527384965120/92093181847303999695573321:ℝ)]]
theorem admission20_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6256963660060228557559495235/31434472737213098562755693568:ℝ) admission20_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission20_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_11_coefficients]
def admission20_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission20_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission20_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission20_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_12_coefficients]
def admission20_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission20_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission20_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission20_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_13_coefficients]
def admission20_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission20_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission20_14_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission20_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_14_coefficients]
theorem admission20_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission20_00_pos hδ hp
 · exact admission20_01_pos hδ hp
 · exact admission20_02_pos hδ hp
 · exact admission20_03_pos hδ hp
 · exact admission20_04_pos hδ hp
 · exact admission20_05_pos hδ hp
 · exact admission20_06_pos hδ hp
 · exact admission20_07_pos hδ hp
 · exact admission20_08_pos hδ hp
 · exact admission20_09_pos hδ hp
 · exact admission20_10_pos hδ hp
 · exact admission20_11_pos hδ hp
 · exact admission20_12_pos hδ hp
 · exact admission20_13_pos hδ hp
 · exact admission20_14_pos hδ hp
#print axioms admission20_all
end
end LewkoStage1Return.C30
