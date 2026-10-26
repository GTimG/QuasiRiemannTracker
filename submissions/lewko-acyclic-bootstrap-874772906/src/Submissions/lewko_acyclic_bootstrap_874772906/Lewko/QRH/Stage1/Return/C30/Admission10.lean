/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission10_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(103152429843767/3198839752287:ℝ), (95953590091480/3198839752287:ℝ)]]
theorem admission10_00_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission10_00_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 0 := by
 rw [admission10_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_00_coefficients]
def admission10_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(74362872073184/3198839752287:ℝ), (70362872073184/3198839752287:ℝ)]]
theorem admission10_01_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission10_01_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 1 := by
 rw [admission10_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_01_coefficients]
def admission10_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12563724471100/1066279917429:ℝ), (11921331012848/1066279917429:ℝ)]]
theorem admission10_02_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (745083188303/2132559834858:ℝ) admission10_02_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 2 := by
 rw [admission10_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_02_coefficients]
def admission10_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(737538086104149152/28789557770583:ℝ), (468125334006788320/9596519256861:ℝ), (667521915916215808/28789557770583:ℝ)],
![(702338591217192320/28789557770583:ℝ), (444711915465930880/9596519256861:ℝ), (632517155180600320/28789557770583:ℝ)]]
theorem admission10_03_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (617692534356055/1228354464878208:ℝ) admission10_03_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 3 := by
 rw [admission10_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_03_coefficients]
def admission10_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4284588293409412/1066279917429:ℝ), (7896467445608416/1066279917429:ℝ), (3624084627905792/1066279917429:ℝ)],
![(4700834236636528/1066279917429:ℝ), (2897851195929472/355426639143:ℝ), (1335189073438976/355426639143:ℝ)]]
theorem admission10_04_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (14156580577757/181978439241216:ℝ) admission10_04_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 4 := by
 rw [admission10_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_04_coefficients]
def admission10_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5169362158365660742/1999274845179375:ℝ), (6223866851818645946/1199564907107625:ℝ), (15578202733145565004/5997824535538125:ℝ)],
![(755608622792817644/399854969035875:ℝ), (4595768280196111664/1199564907107625:ℝ), (2321985559006988732/1199564907107625:ℝ)]]
theorem admission10_05_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (188902155698204411/4367482541789184000:ℝ) admission10_05_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 5 := by
 rw [admission10_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_05_coefficients]
def admission10_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(703258844000981628752333130719168/3407447728350247988736212877:ℝ), (645200706720698562929686723838272/1135815909450082662912070959:ℝ), (1768012275512934343995384033747968/3407447728350247988736212877:ℝ), (535600063262352383646656992952320/3407447728350247988736212877:ℝ)],
![(760988703718991760282382422821120/3407447728350247988736212877:ℝ), (701019350108074580021090387956480/1135815909450082662912070959:ℝ), (1929966743911587225716371880652800/3407447728350247988736212877:ℝ), (587824833001652192975483139604480/3407447728350247988736212877:ℝ)]]
theorem admission10_06_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (32690433548727562478433654355/290768872819221161705490165504:ℝ) admission10_06_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 6 := by
 rw [admission10_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_06_coefficients]
def admission10_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(406102707231618102106885547044/30697727282434666565191107:ℝ), (766884323539727100159044093408/30697727282434666565191107:ℝ), (361470664955126166978605872640/30697727282434666565191107:ℝ)],
![(362226609723894887784014310640/30697727282434666565191107:ℝ), (681869644083418805315264996480/30697727282434666565191107:ℝ), (320290462618466223905093811200/30697727282434666565191107:ℝ)]]
theorem admission10_07_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (312783654900845921782318175/1309769697383879106781487232:ℝ) admission10_07_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 7 := by
 rw [admission10_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_07_coefficients]
def admission10_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1369832264263172575332292334898954335184163859/12790719701014444402162961250000000000000000:ℝ), (156016779816526912946191449850023820489599570439/38372159103043333206488883750000000000000000:ℝ), (179095534976640648538155899095249233861972241139/23023295461825999923893330250000000000000000:ℝ), (439322671958913128027141527253348571607719969109/115116477309129999619466651250000000000000000:ℝ)],
![(127618525485721157438990351615480343913690801301/12790719701014444402162961250000000000000000:ℝ), (1239882007443037403702388862669084323466387223629/38372159103043333206488883750000000000000000:ℝ), (3994780287543671274760354992208758363460887803647/115116477309129999619466651250000000000000000:ℝ), (1423245043161756923758781305912495093284943344469/115116477309129999619466651250000000000000000:ℝ)]]
theorem admission10_08_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1369832264263172575332292334898954335184163859/17882722268281229404589905674240000000000000000000:ℝ) admission10_08_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 8 := by
 rw [admission10_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_08_coefficients]
def admission10_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1866313134592440604998785445241219884833/71947798318206249762166657031250000:ℝ), (340194727695533434196931956375454429551/4796519887880416650811110468750000:ℝ), (288455162059668572759073980568541478162/4496737394887890610135416064453125:ℝ), (17236236557694741264773319285896151152/899347478977578122027083212890625:ℝ)],
![(54491262673269969903500998865869287403/3597389915910312488108332851562500:ℝ), (47905906125920529832226598770444502617/1199129971970104162702777617187500:ℝ), (31058174305763911470964297653855043192/899347478977578122027083212890625:ℝ), (1750901845668840906617803222091547616/179869495795515624405416642578125:ℝ)]]
theorem admission10_09_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (54715682677151278331806350690360863/7858618184303274640688923392000000000:ℝ) admission10_09_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 9 := by
 rw [admission10_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_09_coefficients]
def admission10_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(447372634173436556780728564/1405740125516748046875:ℝ), (134753265007254375738107096/156193347279638671875:ℝ), (1085047348821859010499992036/1405740125516748046875:ℝ), (35520416523472909515306304/156193347279638671875:ℝ)],
![(28767240543131098235989856/56229605020669921875:ℝ), (127843173032121398003510464/93716008367783203125:ℝ), (112027692420107978877071648/93716008367783203125:ℝ), (96407929629615233800632832/281148025103349609375:ℝ)],
![(10436228779082801592186688/56229605020669921875:ℝ), (8980093517249515696489088/18743201673556640625:ℝ), (22612809638606791902374464/56229605020669921875:ℝ), (6110670365941046405093888/56229605020669921875:ℝ)]]
theorem admission10_10_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (11934903058478606259949/6551223812683776000000000:ℝ) admission10_10_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 10 := by
 rw [admission10_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_10_coefficients]
def admission10_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(333674158988816745499707401020/30697727282434666565191107:ℝ), (630135674272768418950320361856/30697727282434666565191107:ℝ), (297124008963403447376019921920/30697727282434666565191107:ℝ)],
![(296793163113744967343472361360/30697727282434666565191107:ℝ), (558723481222958110582645168640/30697727282434666565191107:ℝ), (262549793770718191717183969280/30697727282434666565191107:ℝ)]]
theorem admission10_11_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (128198141489608492049406235/654884848691939553390743616:ℝ) admission10_11_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 11 := by
 rw [admission10_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_11_coefficients]
def admission10_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission10_12_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission10_12_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 12 := by
 rw [admission10_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_12_coefficients]
def admission10_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(77552311962667713/20000000000000000000:ℝ)]]
theorem admission10_13_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (77552311962667713/20000000000000000000:ℝ) admission10_13_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 13 := by
 rw [admission10_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_13_coefficients]
def admission10_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission10_14_identity (δ p : ℝ) : admissionGuard .weakC2 δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission10_14_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC2 δ p 14 := by
 rw [admission10_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_14_coefficients]
theorem admission10_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .weakC2 δ p j := by
 fin_cases j
 · exact admission10_00_pos hδ hp
 · exact admission10_01_pos hδ hp
 · exact admission10_02_pos hδ hp
 · exact admission10_03_pos hδ hp
 · exact admission10_04_pos hδ hp
 · exact admission10_05_pos hδ hp
 · exact admission10_06_pos hδ hp
 · exact admission10_07_pos hδ hp
 · exact admission10_08_pos hδ hp
 · exact admission10_09_pos hδ hp
 · exact admission10_10_pos hδ hp
 · exact admission10_11_pos hδ hp
 · exact admission10_12_pos hδ hp
 · exact admission10_13_pos hδ hp
 · exact admission10_14_pos hδ hp
#print axioms admission10_all
end
end LewkoStage1Return.C30
