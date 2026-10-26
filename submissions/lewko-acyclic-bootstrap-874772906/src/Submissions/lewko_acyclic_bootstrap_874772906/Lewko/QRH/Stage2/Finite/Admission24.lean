/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission24_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19140788478132169/157396201727529:ℝ),(18783392276404640/157396201727529:ℝ)]]
theorem admission24_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission24_00_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission24_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_00_coefficients]
def admission24_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13946713821123712/157396201727529:ℝ),(13746713821123712/157396201727529:ℝ)]]
theorem admission24_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission24_01_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission24_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_01_coefficients]
def admission24_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363448735396138/52465400575843:ℝ),(2331373351478144/52465400575843:ℝ)]]
theorem admission24_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission24_02_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission24_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_02_coefficients]
def admission24_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4096719118843136997248/1416565815547761:ℝ),(898173100314018806656/157396201727529:ℝ),(3987124983983032262656/1416565815547761:ℝ)],
![(4069231117784625336320/1416565815547761:ℝ),(892069708920528424960/157396201727529:ℝ),(3959684262500130488320/1416565815547761:ℝ)]]
theorem admission24_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (30209993457795185/60440141463371136:ℝ) admission24_03_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission24_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_03_coefficients]
def admission24_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24796931043204111126/52465400575843:ℝ),(48515886281802743424/52465400575843:ℝ),(23724055224641593344/52465400575843:ℝ)],
![(25102094478850939456/52465400575843:ℝ),(49119433431054856192/52465400575843:ℝ),(24022471013630795776/52465400575843:ℝ)]]
theorem admission24_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8688008505117771/107449140379326464:ℝ) admission24_04_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission24_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_04_coefficients]
def admission24_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8314088425842997140386/32790875359901875:ℝ),(149996560632425564189752/295117878239116875:ℝ),(75155977665846934042528/295117878239116875:ℝ)],
![(1592870165599217812448/6558175071980375:ℝ),(28748357517614018579264/59023575647823375:ℝ),(14409751258115819347232/59023575647823375:ℝ)]]
theorem admission24_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (149331578024926669917/3438372492138446848000:ℝ) admission24_05_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission24_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_05_coefficients]
def admission24_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(736567310400596519508997040089152005632/8249596917978249986997496465053:ℝ),(239719925090003785220682999243584452096/916621879775361109666388496117:ℝ),(2105774580417608259436638078504615165952/8249596917978249986997496465053:ℝ),(684861132993069630096290925401507102720/8249596917978249986997496465053:ℝ)],
![(744740133481864092832999210700485181440/8249596917978249986997496465053:ℝ),(242421041536304163768251804043895521280/916621879775361109666388496117:ℝ),(2129878401213446649846565185812310261760/8249596917978249986997496465053:ℝ),(692827719847087903368370160117735751680/8249596917978249986997496465053:ℝ)]]
theorem admission24_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1306268945680751095001775599291815/11263449658679637315580581840285696:ℝ) admission24_06_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission24_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_06_coefficients]
def admission24_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(102923316281873349116316514278211402/74320692954759008891869337523:ℝ),(202578917917788632564300318204507008/74320692954759008891869337523:ℝ),(99668544063325707159794489788252160/74320692954759008891869337523:ℝ)],
![(101320890748976241258592100558196160/74320692954759008891869337523:ℝ),(199400115950146429772691166932029440/74320692954759008891869337523:ℝ),(98092064455997181036001606821478400/74320692954759008891869337523:ℝ)]]
theorem admission24_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (374191530059803699630743434225/1585508116368192189693212533824:ℝ) admission24_07_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission24_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_07_coefficients]
def admission24_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(99478843818427617467558661556467555449653026101015889/43009660274744796812424385140625000000000000000:ℝ),(8450789723400613225076207223374962729299001305557800309/1161260827418109513935458398796875000000000000000:ℝ),(26530582048487389790322067348444324969040122284334572829/3483782482254328541806375196390625000000000000000:ℝ),(9235888543564789226366791081283503606185235356843458911/3483782482254328541806375196390625000000000000000:ℝ)],
![(123882106392448630453020926249642940861953560702429551/43009660274744796812424385140625000000000000000:ℝ),(10403283613531431233476642616716597402412731650027880351/1161260827418109513935458398796875000000000000000:ℝ),(32316134244080566871182994189009080912125211400701789213/3483782482254328541806375196390625000000000000000:ℝ),(11140622641135343906782195394655405740989754867514941791/3483782482254328541806375196390625000000000000000:ℝ)]]
theorem admission24_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (298436531455282852402675984669402666348959078303047667/92362542146049638527763890325946368000000000000000000000:ℝ) admission24_08_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission24_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_08_coefficients]
def admission24_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(27586052109554206433762341306663477597993339/4354728102817910677257968995488281250:ℝ),(26559482002529543140696879540525361974167989/1451576034272636892419322998496093750:ℝ),(38305578051821280610840750860665215941316544/2177364051408955338628984497744140625:ℝ),(2451887724856778061637758572340676922218496/435472810281791067725796899548828125:ℝ)],
![(2487763601623889370472587255652859077014352/435472810281791067725796899548828125:ℝ),(2388215624606068063618447666988626565989808/145157603427263689241932299849609375:ℝ),(6867173462278116030470393194066953601288192/435472810281791067725796899548828125:ℝ),(438060353346765623311099943929180471066624/87094562056358213545159379909765625:ℝ)]]
theorem admission24_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (13368541056725025125460813718541884493/1902609739641830627631855040588800000000:ℝ) admission24_09_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission24_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_09_coefficients]
def admission24_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8077846707301600796965577334592/13833650542458603515625:ℝ),(7709571758693279200930880858176/4611216847486201171875:ℝ),(489490814943407030076465958784/307414456499080078125:ℝ),(6976248322370392047613902905344/13833650542458603515625:ℝ)],
![(3051961010366834323900515463168/2766730108491720703125:ℝ),(12917101212625499545259307008/4098859419987734375:ℝ),(8283444112829752051000438071296/2766730108491720703125:ℝ),(872124656058124727283640434688/922243369497240234375:ℝ)],
![(287030521234260716620245434368/553346021698344140625:ℝ),(272641588630413564757050195968/184448673899448046875:ℝ),(774878166925627014297564872704/553346021698344140625:ℝ),(243985146268647036646659719168/553346021698344140625:ℝ)]]
theorem admission24_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (58170591895257720147767/32234742113797939200000000:ℝ) admission24_10_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission24_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_10_coefficients]
def admission24_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(84370757420459682450190173314714422/74320692954759008891869337523:ℝ),(166068476463221114014788595618639616/74320692954759008891869337523:ℝ),(3026299807566796579074049996922880/2752618257583666995995160649:ℝ)],
![(83023239427416708607965322201115200/74320692954759008891869337523:ℝ),(163395799576686014423650441658408960/74320692954759008891869337523:ℝ),(8931647686032407975577132498288640/8257854772751000987985481947:ℝ)]]
theorem admission24_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (68143064010867370419137058245/352335136970709375487380563072:ℝ) admission24_11_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission24_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_11_coefficients]
def admission24_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission24_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission24_12_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission24_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_12_coefficients]
def admission24_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission24_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission24_13_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission24_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_13_coefficients]
def admission24_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission24_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission24_14_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission24_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_14_coefficients]
theorem admission24_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission24_00_pos hδ hp
 · exact admission24_01_pos hδ hp
 · exact admission24_02_pos hδ hp
 · exact admission24_03_pos hδ hp
 · exact admission24_04_pos hδ hp
 · exact admission24_05_pos hδ hp
 · exact admission24_06_pos hδ hp
 · exact admission24_07_pos hδ hp
 · exact admission24_08_pos hδ hp
 · exact admission24_09_pos hδ hp
 · exact admission24_10_pos hδ hp
 · exact admission24_11_pos hδ hp
 · exact admission24_12_pos hδ hp
 · exact admission24_13_pos hδ hp
 · exact admission24_14_pos hδ hp
#print axioms admission24_all
end
end LewkoStage2Finite
