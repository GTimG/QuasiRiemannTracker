/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission20_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19140788478132169/157396201727529:ℝ),(18783392276404640/157396201727529:ℝ)]]
theorem admission20_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission20_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission20_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_00_coefficients]
def admission20_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13946713821123712/157396201727529:ℝ),(13746713821123712/157396201727529:ℝ)]]
theorem admission20_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission20_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission20_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_01_coefficients]
def admission20_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363448735396138/52465400575843:ℝ),(2331373351478144/52465400575843:ℝ)]]
theorem admission20_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission20_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission20_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_02_coefficients]
def admission20_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2075871200267885102848/1416565815547761:ℝ),(455192668193589223168/157396201727529:ℝ),(2021003213474417905664/1416565815547761:ℝ)],
![(2048383199209373441920/1416565815547761:ℝ),(449089276800098841472/157396201727529:ℝ),(1993562491991516131328/1416565815547761:ℝ)]]
theorem admission20_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (486709592771366243/967042263413938176:ℝ) admission20_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission20_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_03_coefficients]
def admission20_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(12164532209873714892/52465400575843:ℝ),(23800246100507006208/52465400575843:ℝ),(11638215770578894848/52465400575843:ℝ)],
![(12469695645520543222/52465400575843:ℝ),(24403793249759118976/52465400575843:ℝ),(11936631559568097280/52465400575843:ℝ)]]
theorem admission20_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131020954085491/26862285094831616:ℝ) admission20_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission20_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_04_coefficients]
def admission20_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4506781810768406648339/32790875359901875:ℝ),(16246560300424763266342/59023575647823375:ℝ),(40665001705514136629159/295117878239116875:ℝ)],
![(4157044212921498570193/32790875359901875:ℝ),(74978028457768345038278/295117878239116875:ℝ),(37557780330246299322791/295117878239116875:ℝ)]]
theorem admission20_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (12471132638764495710579/275069799371075747840000:ℝ) admission20_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission20_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_05_coefficients]
def admission20_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(361999360718910604722554690164747725824/8249596917978249986997496465053:ℝ),(117799934589055893107008101100382784512/916621879775361109666388496117:ℝ),(1034656379436587658965606656402279399424/8249596917978249986997496465053:ℝ),(336455626356021110094086036663582064640/8249596917978249986997496465053:ℝ)],
![(370172183800178178046556860776080901632/8249596917978249986997496465053:ℝ),(120501051035356271654576905900693853696/916621879775361109666388496117:ℝ),(1058760200232426049375533763709974495232/8249596917978249986997496465053:ℝ),(344422213210039383366165271379810713600/8249596917978249986997496465053:ℝ)]]
theorem admission20_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320869089466115102857671772636015/2815862414669909328895145460071424:ℝ) admission20_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission20_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_06_coefficients]
def admission20_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(53077056636618073282848436235741684/74320692954759008891869337523:ℝ),(104481182303029094345771003044196096/74320692954759008891869337523:ℝ),(51410751638991379703690127860899840/74320692954759008891869337523:ℝ)],
![(51474631103720965425124022515726442/74320692954759008891869337523:ℝ),(101302380335386891554161851771718528/74320692954759008891869337523:ℝ),(49834272031662853579897244894126080/74320692954759008891869337523:ℝ)]]
theorem admission20_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (6083285160115094431139800402115/25368129861891075035091400541184:ℝ) admission20_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission20_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_07_coefficients]
def admission20_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(15718487489349024497341316129176119332800556049723849/21504830137372398406212192570312500000000000000:ℝ),(1389576113937928069402141550892717009388081306554830029/580630413709054756967729199398437500000000000000:ℝ),(4517228667484629445235070576853121280642099949362050869/1741891241127164270903187598195312500000000000000:ℝ),(1621670663399169565713560825347151632341547944725192551/1741891241127164270903187598195312500000000000000:ℝ)],
![(698002969408988274751811211894095300973770583760767/537620753434309960155304814257812500000000000:ℝ),(47316461180066741472047184951270686918898929575797401/11612608274181095139354583987968750000000000000:ℝ),(7410004765281217985665533997135499252184644507545659061/1741891241127164270903187598195312500000000000000:ℝ),(2574037712184446905921262982033102699743807700060933991/1741891241127164270903187598195312500000000000000:ℝ)]]
theorem admission20_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (47155462468047073492023948387528357998401668149171547/23090635536512409631940972581486592000000000000000000000:ℝ) admission20_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission20_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_08_coefficients]
def admission20_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(8273860202067661292512289757530098103172259/2177364051408955338628984497744140625:ℝ),(7993899922676657800852874906373726312030989/725788017136318446209661499248046875:ℝ),(23145460450634566405036611370617470621331328/2177364051408955338628984497744140625:ℝ),(1487529820551338975901138138865113027994624/435472810281791067725796899548828125:ℝ)],
![(13839304310820009855988110764925309378494699/4354728102817910677257968995488281250:ℝ),(13310474088884453097193346942108356309792069/1451576034272636892419322998496093750:ℝ),(19175749710203865946547826480287022686455744/2177364051408955338628984497744140625:ℝ),(1225943862428389030818879286170338461109248/435472810281791067725796899548828125:ℝ)]]
theorem admission20_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1197210803152723662909061802900721153427/152208779171346450210548403247104000000000:ℝ) admission20_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission20_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_09_coefficients]
def admission20_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2459781792163825342750083251456/13833650542458603515625:ℝ),(2361503101655590559564135981312/4611216847486201171875:ℝ),(754512420447979923723936237056/1537072282495400390625:ℝ),(2165891543510122977573101441024/13833650542458603515625:ℝ)],
![(4490205343971294419378470192384/13833650542458603515625:ℝ),(95504134354887809290766781696/102471485499693359375:ℝ),(12317286333349008033457280480768/13833650542458603515625:ℝ),(1304816090147232732860745048064/4611216847486201171875:ℝ)],
![(404845647626283233919504563776/2766730108491720703125:ℝ),(1930055554564292189960784568384/4611216847486201171875:ℝ),(5508494830762420175819753953664/13833650542458603515625:ℝ),(1742563865146272275534923067392/13833650542458603515625:ℝ)]]
theorem admission20_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (425430631139226629769268327/206302349528306810880000000000:ℝ) admission20_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission20_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_10_coefficients]
def admission20_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(43544022884788384061029784611596044/74320692954759008891869337523:ℝ),(85717987931401370539296371317345792/74320692954759008891869337523:ℝ),(4686701448018176630256092487864320/8257854772751000987985481947:ℝ)],
![(42196504891745410218804933497996822/74320692954759008891869337523:ℝ),(83045311044866270948158217357115136/74320692954759008891869337523:ℝ),(1513149903783398289537024998461440/2752618257583666995995160649:ℝ)]]
theorem admission20_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1108264089685106169094500731295/5637362191531350007798089009152:ℝ) admission20_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission20_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_11_coefficients]
def admission20_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission20_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission20_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission20_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_12_coefficients]
def admission20_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission20_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission20_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage2Finite
