/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission21_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19140788478132169/157396201727529:ℝ),(18783392276404640/157396201727529:ℝ)]]
theorem admission21_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission21_00_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission21_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_00_coefficients]
def admission21_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13946713821123712/157396201727529:ℝ),(13746713821123712/157396201727529:ℝ)]]
theorem admission21_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission21_01_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission21_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_01_coefficients]
def admission21_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363448735396138/52465400575843:ℝ),(2331373351478144/52465400575843:ℝ)]]
theorem admission21_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission21_02_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission21_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_02_coefficients]
def admission21_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4110486759160197771008/1416565815547761:ℝ),(300409174217951145216/52465400575843:ℝ),(4000845344724483149824/1416565815547761:ℝ)],
![(4082998758101686110080/1416565815547761:ℝ),(298374710420121017984/52465400575843:ℝ),(3973404623241581375488/1416565815547761:ℝ)]]
theorem admission21_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (970069488096089203/1934084526827876352:ℝ) admission21_03_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission21_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_03_coefficients]
def admission21_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24640975502051884012/52465400575843:ℝ),(48210754921539833088/52465400575843:ℝ),(23574847330146992128/52465400575843:ℝ)],
![(24946138937698712342/52465400575843:ℝ),(48814302070791945856/52465400575843:ℝ),(23873263119136194560/52465400575843:ℝ)]]
theorem admission21_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4316683471096251/53724570189663232:ℝ) admission21_04_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission21_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_04_coefficients]
def admission21_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8488957224766451179459/32790875359901875:ℝ),(30620739059231772555974/59023575647823375:ℝ),(76689379850803684997239/295117878239116875:ℝ)],
![(8139219626919543101313/32790875359901875:ℝ),(146848922251803391486438/295117878239116875:ℝ),(73582158475535847690871/295117878239116875:ℝ)]]
theorem admission21_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (24417658880758629303939/550139598742151495680000:ℝ) admission21_05_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission21_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_05_coefficients]
def admission21_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(732377780746338082821034486835933154304/8249596917978249986997496465053:ℝ),(238346573119373118885127400229311491072/916621879775361109666388496117:ℝ),(2093620639902797278934829823271263043584/8249596917978249986997496465053:ℝ),(680877839566060493460251308043392778240/8249596917978249986997496465053:ℝ)],
![(740550603827605656145036657447266330112/8249596917978249986997496465053:ℝ),(241047689565673497432696205029622560256/916621879775361109666388496117:ℝ),(2117724460698635669344756930578958139392/8249596917978249986997496465053:ℝ),(688844426420078766732330542759621427200/8249596917978249986997496465053:ℝ)]]
theorem admission21_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (649335708204327100239039714854615/5631724829339818657790290920142848:ℝ) admission21_06_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission21_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_06_coefficients]
def admission21_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(103737502011106193912144486514839764/74320692954759008891869337523:ℝ),(204181240278102309232116586510210816/74320692954759008891869337523:ℝ),(100456783866989970221690931271639040/74320692954759008891869337523:ℝ)],
![(102135076478209086054420072794824522/74320692954759008891869337523:ℝ),(201002438310460106440507435237733248/74320692954759008891869337523:ℝ),(98880304259661444097898048304865280/74320692954759008891869337523:ℝ)]]
theorem admission21_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (12070349641071953625231695349715/50736259723782150070182801082368:ℝ) admission21_07_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission21_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_07_coefficients]
def admission21_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(43638606265708555487413764604939931371751379400154529/21504830137372398406212192570312500000000000000:ℝ),(3743313983758823121293496775053465582691721306222486789/580630413709054756967729199398437500000000000000:ℝ),(11855013127818882893597402834050189176774774061019558189/1741891241127164270903187598195312500000000000000:ℝ),(4159743290121042785931304243992602290289443748764614671/1741891241127164270903187598195312500000000000000:ℝ)],
![(698002969408988274751811211894095300973770583760767/268810376717154980077652407128906250000000000:ℝ),(471956092882423212549371447172428291924858647845752681/58063041370905475696772919939843750000000000000:ℝ),(14747789225615471434027866254332567148317318619203166381/1741891241127164270903187598195312500000000000000:ℝ),(5112110338906320126139006400678553357691703504100356111/1741891241127164270903187598195312500000000000000:ℝ)]]
theorem admission21_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (130915818797125666462241293814819794115254138200463587/46181271073024819263881945162973184000000000000000000000:ℝ) admission21_08_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission21_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_08_coefficients]
def admission21_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(14493269206127384718693757896662245795708139/2177364051408955338628984497744140625:ℝ),(13964438984191827959898994073845292727005509/725788017136318446209661499248046875:ℝ),(40313394106329856481212594355784854624551808/2177364051408955338628984497744140625:ℝ),(2582680703918253034178887998688064205661184/435472810281791067725796899548828125:ℝ)],
![(26278122318939456708351047043189604763566459/4354728102817910677257968995488281250:ℝ),(25251552211914793415285585277051489139741109/1451576034272636892419322998496093750:ℝ),(36343683365899156022723809465454406689676224/2177364051408955338628984497744140625:ℝ),(2321094745795303089096629145993289638775808/435472810281791067725796899548828125:ℝ)]]
theorem admission21_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2266694087690725672945926900384071912867/304417558342692900421096806494208000000000:ℝ) admission21_09_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission21_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_09_coefficients]
def admission21_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(947692213729718866515509511424/1537072282495400390625:ℝ),(8152539189298973880092632600832/4611216847486201171875:ℝ),(23330930236175096064027498796544/13833650542458603515625:ℝ),(7402572431626894222389186596864/13833650542458603515625:ℝ)],
![(5391654037239338478970774032128/4611216847486201171875:ℝ),(3085985700983042736771878624512/922243369497240234375:ℝ),(44061267128701856764419452446208/13833650542458603515625:ℝ),(13946503782955481149753595174912/13833650542458603515625:ℝ)],
![(509302458298299515416124824768/922243369497240234375:ℝ),(2423753975288723711735725298368/1537072282495400390625:ℝ),(6904052391323997385423284418688/4611216847486201171875:ℝ),(2179312829847761327296732647424/4611216847486201171875:ℝ)]]
theorem admission21_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (532058796349551105297053869/275069799371075747840000000000:ℝ) admission21_10_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission21_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_10_coefficients]
def admission21_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(85055642598496738365012445712153644/74320692954759008891869337523:ℝ),(167415887719744377751121592146550272/74320692954759008891869337523:ℝ),(9152525291034380618044658737008640/8257854772751000987985481947:ℝ)],
![(83708124605453764522787594598554422/74320692954759008891869337523:ℝ),(164743210833209278159983438186319616/74320692954759008891869337523:ℝ),(9005273554366398856399641244528640/8257854772751000987985481947:ℝ)]]
theorem admission21_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2198553113858984095800693663215/11274724383062700015596178018304:ℝ) admission21_11_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission21_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_11_coefficients]
def admission21_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission21_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission21_12_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission21_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_12_coefficients]
def admission21_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission21_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission21_13_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission21_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_13_coefficients]
def admission21_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission21_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission21_14_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission21_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_14_coefficients]
theorem admission21_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission21_00_pos hδ hp
 · exact admission21_01_pos hδ hp
 · exact admission21_02_pos hδ hp
 · exact admission21_03_pos hδ hp
 · exact admission21_04_pos hδ hp
 · exact admission21_05_pos hδ hp
 · exact admission21_06_pos hδ hp
 · exact admission21_07_pos hδ hp
 · exact admission21_08_pos hδ hp
 · exact admission21_09_pos hδ hp
 · exact admission21_10_pos hδ hp
 · exact admission21_11_pos hδ hp
 · exact admission21_12_pos hδ hp
 · exact admission21_13_pos hδ hp
 · exact admission21_14_pos hδ hp
#print axioms admission21_all
end
end LewkoStage2Finite
