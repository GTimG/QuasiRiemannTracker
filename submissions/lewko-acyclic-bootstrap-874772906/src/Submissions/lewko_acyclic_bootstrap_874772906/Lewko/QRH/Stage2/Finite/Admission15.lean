/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission15_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission15_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission15_00_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission15_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_00_coefficients]
def admission15_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission15_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission15_01_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission15_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_01_coefficients]
def admission15_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission15_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission15_02_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission15_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_02_coefficients]
def admission15_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1833029868706053161216/157396201727529:ℝ),(32774782012081428793600/1416565815547761:ℝ),(16277788593726950342656/1416565815547761:ℝ)],
![(1820823285919072397824/157396201727529:ℝ),(32555158081066994825728/1416565815547761:ℝ),(16168025707795343245312/1416565815547761:ℝ)]]
theorem admission15_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (493408987664652809/967042263413938176:ℝ) admission15_03_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission15_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_03_coefficients]
def admission15_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93375103774190015898/52465400575843:ℝ),(184685427671146507008/52465400575843:ℝ),(91315231430695944192/52465400575843:ℝ)],
![(94582230148078159428/52465400575843:ℝ),(187086185125607542272/52465400575843:ℝ),(92508894586652753920/52465400575843:ℝ)]]
theorem admission15_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8360159127566157/107449140379326464:ℝ) admission15_04_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission15_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_04_coefficients]
def admission15_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(337131696770218523929096/295117878239116875:ℝ),(674436753142704942652948/295117878239116875:ℝ),(112430596502567331712534/98372626079705625:ℝ)],
![(324622063969973042625982/295117878239116875:ℝ),(649498321552922650840612/295117878239116875:ℝ),(21657526933775376394142/19674525215941125:ℝ)]]
theorem admission15_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (162311031984986521312991/3300837592452908974080000:ℝ) admission15_05_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission15_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_05_coefficients]
def admission15_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5488560761630781170953208135348682658816/8249596917978249986997496465053:ℝ),(16263808622693014537115762808777977009152/8249596917978249986997496465053:ℝ),(16062940218487147229063792843451863597056/8249596917978249986997496465053:ℝ),(5287690979448118482240425770022569246720/8249596917978249986997496465053:ℝ)],
![(5553114040378608814887335891186739202048/8249596917978249986997496465053:ℝ),(16456643523033884552244185132711728531456/8249596917978249986997496465053:ℝ),(16254954543918720069968452089277387767808/8249596917978249986997496465053:ℝ),(5351423674280264668417059647752398438400/8249596917978249986997496465053:ℝ)]]
theorem admission15_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1260683770048169727859598581796305/11263449658679637315580581840285696:ℝ) admission15_06_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission15_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_06_coefficients]
def admission15_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(424399265622252395993655414425284870/74320692954759008891869337523:ℝ),(841977635700586527267088410831753472/74320692954759008891869337523:ℝ),(417591931541245142124692554754293760/74320692954759008891869337523:ℝ)],
![(418041558514384559220528966466018300/74320692954759008891869337523:ℝ),(829314113335988017188698576419703296/74320692954759008891869337523:ℝ),(411286013111931037629521022887198720/74320692954759008891869337523:ℝ)]]
theorem admission15_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (6275726518431564905235611311145/25368129861891075035091400541184:ℝ) admission15_07_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission15_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_07_coefficients]
def admission15_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10123080878394106198991814932466238698039139951627834919/1741891241127164270903187598195312500000000000000:ℝ),(6717732465691495829489693407746212577585741856444426693/348378248225432854180637519639062500000000000000:ℝ),(36803635055034747055050778051911871208153206444453858187/1741891241127164270903187598195312500000000000000:ℝ),(13338000351342286435994652216037612457080913676359559641/1741891241127164270903187598195312500000000000000:ℝ)],
![(715411879776802004725674212780824914234108457328382317/69675649645086570836127503927812500000000000000:ℝ),(56731450682747951375617839840001185197853637080381254999/1741891241127164270903187598195312500000000000000:ℝ),(11960628806328885859853011522654559180630100348243437647/348378248225432854180637519639062500000000000000:ℝ),(20956936741624505157656269469525220996298991719045491161/1741891241127164270903187598195312500000000000000:ℝ)]]
theorem admission15_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (10123080878394106198991814932466238698039139951627834919/9975154551773360960998500155202207744000000000000000000000:ℝ) admission15_08_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission15_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_08_coefficients]
def admission15_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(136693974034360997268206478372097886214205979/2177364051408955338628984497744140625:ℝ),(402836838885222439684733894788832319408829721/2177364051408955338628984497744140625:ℝ),(395608633469028617145359355151032229535389952/2177364051408955338628984497744140625:ℝ),(25893164793805023175076281043400004982996992/435472810281791067725796899548828125:ℝ)],
![(126046136821954596963019560537267477559573742/2177364051408955338628984497744140625:ℝ),(371078439910404551984773781034750001719956378/2177364051408955338628984497744140625:ℝ),(364034633019928818606468684428023963782765056/2177364051408955338628984497744140625:ℝ),(23800477128821423614418210221841808447913984/435472810281791067725796899548828125:ℝ)]]
theorem admission15_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1452665840382166968653455213735461941401/152208779171346450210548403247104000000000:ℝ) admission15_09_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission15_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_09_coefficients]
def admission15_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16105851516163799547133392669568/2766730108491720703125:ℝ),(78868075626775679083607740279424/4611216847486201171875:ℝ),(77209780575825538109458607211008/4611216847486201171875:ℝ),(75554400409038887313219564142592/13833650542458603515625:ℝ)],
![(17175314890432170049598714277376/1537072282495400390625:ℝ),(453857738496487523425912091989504/13833650542458603515625:ℝ),(443998949273207294883701418489856/13833650542458603515625:ℝ),(16079900124279505767130861666304/1537072282495400390625:ℝ)],
![(73999826369804202308415536117248/13833650542458603515625:ℝ),(217108071232729182314397698002432/13833650542458603515625:ℝ),(42444994866017594206629333530624/2766730108491720703125:ℝ),(69116757815194241027164505767936/13833650542458603515625:ℝ)]]
theorem admission15_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (527319014092973640649143263/206302349528306810880000000000:ℝ) admission15_10_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission15_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_10_coefficients]
def admission15_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(116106301395127243190441734899777022/24773564318253002963956445841:ℝ),(691049454782077453663232438427718144/74320692954759008891869337523:ℝ),(12694206176939113362876269957611520/2752618257583666995995160649:ℝ)],
![(114324481225263940094385680731060396/24773564318253002963956445841:ℝ),(680403038488959911061735500777976832/74320692954759008891869337523:ℝ),(37493611584145413042048739902914560/8257854772751000987985481947:ℝ)]]
theorem admission15_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1144214220707562653871116330045/5637362191531350007798089009152:ℝ) admission15_11_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission15_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_11_coefficients]
def admission15_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission15_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission15_12_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission15_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_12_coefficients]
def admission15_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission15_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission15_13_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission15_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_13_coefficients]
def admission15_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission15_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission15_14_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission15_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_14_coefficients]
theorem admission15_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission15_00_pos hδ hp
 · exact admission15_01_pos hδ hp
 · exact admission15_02_pos hδ hp
 · exact admission15_03_pos hδ hp
 · exact admission15_04_pos hδ hp
 · exact admission15_05_pos hδ hp
 · exact admission15_06_pos hδ hp
 · exact admission15_07_pos hδ hp
 · exact admission15_08_pos hδ hp
 · exact admission15_09_pos hδ hp
 · exact admission15_10_pos hδ hp
 · exact admission15_11_pos hδ hp
 · exact admission15_12_pos hδ hp
 · exact admission15_13_pos hδ hp
 · exact admission15_14_pos hδ hp
#print axioms admission15_all
end
end LewkoStage2Finite
