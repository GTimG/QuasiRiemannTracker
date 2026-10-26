/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission28_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3249697446643283/52465400575843:ℝ),(9391696138202320/157396201727529:ℝ)]]
theorem admission28_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission28_00_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission28_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_00_coefficients]
def admission28_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2357785636853952/52465400575843:ℝ),(6873356910561856/157396201727529:ℝ)]]
theorem admission28_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission28_01_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission28_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_01_coefficients]
def admission28_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1197762059657066/52465400575843:ℝ),(1165686675739072/52465400575843:ℝ)]]
theorem admission28_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission28_02_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission28_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_02_coefficients]
def admission28_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(88213237834060911104/472188605182587:ℝ),(515478070093803610624/1416565815547761:ℝ),(250910356591620877312/1416565815547761:ℝ)],
![(230345659824532928/1265921193519:ℝ),(501733169564547780160/1416565815547761:ℝ),(244050176220895433728/1416565815547761:ℝ)]]
theorem admission28_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (238330250215718197/483521131706969088:ℝ) admission28_03_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission28_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_03_coefficients]
def admission28_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1627673385776890000/52465400575843:ℝ),(3118469315366182400/52465400575843:ℝ),(1492078944946012160/52465400575843:ℝ)],
![(1705667194044962554/52465400575843:ℝ),(3271034995497637568/52465400575843:ℝ),(1566682892193312768/52465400575843:ℝ)]]
theorem admission28_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (273207814626345/3357785636853952:ℝ) admission28_04_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission28_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_04_coefficients]
def admission28_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(973211772565282880471/59023575647823375:ℝ),(1956704054510387735342/59023575647823375:ℝ),(327599529889598374957/19674525215941125:ℝ)],
![(813800332113003603833/59023575647823375:ℝ),(8209744438008121683178/295117878239116875:ℝ),(1379062534842338765921/98372626079705625:ℝ)]]
theorem admission28_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (813800332113003603833/20630234952830681088000:ℝ) admission28_05_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission28_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_05_coefficients]
def admission28_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(670362636571587083357811937645619200/222962078864277026675608012569:ℝ),(71068036553543737389618619706558187520/8249596917978249986997496465053:ℝ),(67791367581393818114996907474908446720/8249596917978249986997496465053:ℝ),(21526388325627461460385329461238169600/8249596917978249986997496465053:ℝ)],
![(25851348468271905387653463190216467712/8249596917978249986997496465053:ℝ),(74158620234233098125744400672696194304/8249596917978249986997496465053:ℝ),(70829852710096563240448971283246477312/8249596917978249986997496465053:ℝ),(22522211682379745619395233800766750720/8249596917978249986997496465053:ℝ)]]
theorem admission28_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41058327342276499672670992777325/351982801833738666111893182508928:ℝ) admission28_06_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission28_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_06_coefficients]
def admission28_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6733022172891646173285840070234480/74320692954759008891869337523:ℝ),(13057626338600787623034415755512320/74320692954759008891869337523:ℝ),(6327813979415889580224210797189120/74320692954759008891869337523:ℝ)],
![(6325877721983508180417781244764582/74320692954759008891869337523:ℝ),(12256465158443949289126281602660416/74320692954759008891869337523:ℝ),(5933694077583758049275990055495680/74320692954759008891869337523:ℝ)]]
theorem admission28_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (2897311561320194359998042019285/12684064930945537517545700270592:ℝ) admission28_07_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission28_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_07_coefficients]
def admission28_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(13270026387693722329917104202036003847090383267898991/174189124112716427090318759819531250000000000000:ℝ),(43268191707760786263297242998189923423864606669145361/174189124112716427090318759819531250000000000000:ℝ),(46727045231657915926867682631819426858020793229749299/174189124112716427090318759819531250000000000000:ℝ),(16727487659849997860167969205353492609802819828502929/174189124112716427090318759819531250000000000000:ℝ)],
![(104324049551064884196687721029035100917652558325047023/696756496450865708361275039278125000000000000000:ℝ),(1615603858143812202591911147208335807157037908406225171/3483782482254328541806375196390625000000000000000:ℝ),(416663416735623645899202186315778555594998331796245999/870945620563582135451593799097656250000000000000:ℝ),(28632075769665964612764246163927880952331066770199697/174189124112716427090318759819531250000000000000:ℝ)]]
theorem admission28_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (13270026387693722329917104202036003847090383267898991/3896544746786469125390039123125862400000000000000000000:ℝ) admission28_08_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission28_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_08_coefficients]
def admission28_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(103460574743331313590910325476153368914098/435472810281791067725796899548828125:ℝ),(291572334221860520678120359459439339188642/435472810281791067725796899548828125:ℝ),(54580983581827796136049002158530297111808/87094562056358213545159379909765625:ℝ),(84796052593116500210000544532357859034496/435472810281791067725796899548828125:ℝ)],
![(273722146503852546299867972515414229545981/1741891241127164270903187598195312500:ℝ),(3776996209969899228885826962721584459073961/8709456205635821354515937990976562500:ℝ),(862570575918550935808264180183347756986384/2177364051408955338628984497744140625:ℝ),(52097807827747757074718187945511038173824/435472810281791067725796899548828125:ℝ)]]
theorem admission28_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (407014123654279352146235843324304985733/76104389585673225105274201623552000000000:ℝ) admission28_09_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission28_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_09_coefficients]
def admission28_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2914084287168608337176708608/512357427498466796875:ℝ),(219086325892142819521631477248/13833650542458603515625:ℝ),(202222861122009438431949557248/13833650542458603515625:ℝ),(20606241161139681338029737472/4611216847486201171875:ℝ)],
![(128162719098721059442598807552/13833650542458603515625:ℝ),(117406489104709545545258465792/4611216847486201171875:ℝ),(106702877691586898022518124032/4611216847486201171875:ℝ),(96055805484353116874377782272/13833650542458603515625:ℝ)],
![(48682392378689462301091724096/13833650542458603515625:ℝ),(130784592904778481782988188576/13833650542458603515625:ℝ),(115588165483547724157908704864/13833650542458603515625:ℝ),(33487974277771204676012240384/13833650542458603515625:ℝ)]]
theorem admission28_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (65406199761271884132836407/51575587382076702720000000000:ℝ) admission28_10_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission28_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_10_coefficients]
def admission28_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(613449437434792701905311894700560/8257854772751000987985481947:ℝ),(10707687707802251794133320504806400/74320692954759008891869337523:ℝ),(576634447460523218679197967703040/8257854772751000987985481947:ℝ)],
![(575394331070527922976749284526794/8257854772751000987985481947:ℝ),(10033982079540619925966822240851072/74320692954759008891869337523:ℝ),(179940504431175926089314531527680/2752618257583666995995160649:ℝ)]]
theorem admission28_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (527169446575710720964788666585/2818681095765675003899044504576:ℝ) admission28_11_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission28_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_11_coefficients]
def admission28_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission28_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission28_12_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission28_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_12_coefficients]
def admission28_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission28_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission28_13_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission28_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_13_coefficients]
def admission28_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission28_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission28_14_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission28_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_14_coefficients]
theorem admission28_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission28_00_pos hδ hp
 · exact admission28_01_pos hδ hp
 · exact admission28_02_pos hδ hp
 · exact admission28_03_pos hδ hp
 · exact admission28_04_pos hδ hp
 · exact admission28_05_pos hδ hp
 · exact admission28_06_pos hδ hp
 · exact admission28_07_pos hδ hp
 · exact admission28_08_pos hδ hp
 · exact admission28_09_pos hδ hp
 · exact admission28_10_pos hδ hp
 · exact admission28_11_pos hδ hp
 · exact admission28_12_pos hδ hp
 · exact admission28_13_pos hδ hp
 · exact admission28_14_pos hδ hp
#print axioms admission28_all
end
end LewkoStage2Finite
