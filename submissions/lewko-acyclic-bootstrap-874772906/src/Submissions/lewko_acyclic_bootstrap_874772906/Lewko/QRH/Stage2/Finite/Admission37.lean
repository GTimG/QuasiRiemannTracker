/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission37_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(50208178137654883/52465400575843:ℝ),(150267138211237120/157396201727529:ℝ)]]
theorem admission37_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission37_00_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission37_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_00_coefficients]
def admission37_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(36724570189663232/52465400575843:ℝ),(109973710568989696/157396201727529:ℝ)]]
theorem admission37_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission37_01_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission37_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_01_coefficients]
def admission37_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(18683062195743146/52465400575843:ℝ),(18650986811825152/52465400575843:ℝ)]]
theorem admission37_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission37_02_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission37_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_02_coefficients]
def admission37_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(344036870813837956956160/472188605182587:ℝ),(2060716412928245841117184/1416565815547761:ℝ),(1028606923686731970248704/1416565815547761:ℝ)],
![(343451338476667759406080/472188605182587:ℝ),(2057203607941829534909440/1416565815547761:ℝ),(1026850717511826256691200/1416565815547761:ℝ)]]
theorem admission37_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3917124624297432925/7736338107311505408:ℝ) admission37_03_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission37_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_03_coefficients]
def admission37_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5992310621374308847200/52465400575843:ℝ),(11951057080871138181120/52465400575843:ℝ),(5958766474536394162176/52465400575843:ℝ)],
![(6011462988515191384074/52465400575843:ℝ),(11989308026431945755648/52465400575843:ℝ),(5977865085031703117824/52465400575843:ℝ)]]
theorem admission37_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131020954085491/26862285094831616:ℝ) admission37_04_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission37_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_04_coefficients]
def admission37_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4016905047327730046310521/59023575647823375:ℝ),(40175379611442290024288122/295117878239116875:ℝ),(2232311140756231959310613/32790875359901875:ℝ)],
![(3977068067911883146356647/59023575647823375:ℝ),(1591093305322297939025098/11804715129564675:ℝ),(442043068861976578804177/6558175071980375:ℝ)]]
theorem admission37_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (3977068067911883146356647/84501442366794469736448000:ℝ) admission37_05_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission37_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_05_coefficients]
def admission37_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1391086701378699743376402414390473615147008/8249596917978249986997496465053:ℝ),(4160279411055925340627981663301242889895936/8249596917978249986997496465053:ℝ),(4147314960851471857122003674284801411514368/8249596917978249986997496465053:ℝ),(1378122245554262466945376406174032136765440/8249596917978249986997496465053:ℝ)],
![(1395178671047822283660632857029248031969280/8249596917978249986997496465053:ℝ),(4172542225509518356977283633291612028784640/8249596917978249986997496465053:ℝ),(4159564698114206073385913500611105201848320/8249596917978249986997496465053:ℝ),(1382201138023519822860680974348741205032960/8249596917978249986997496465053:ℝ)]]
theorem admission37_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320869089466115102857671772636015/2815862414669909328895145460071424:ℝ) admission37_06_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission37_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_06_coefficients]
def admission37_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(26075445872505604861742887997276329888/74320692954759008891869337523:ℝ),(52044566271846958549176487189080162304/74320692954759008891869337523:ℝ),(25969173407121996556559739680223395840/74320692954759008891869337523:ℝ)],
![(25974344332440114554278048259277057430/74320692954759008891869337523:ℝ),(51842570140085026000978811086621680640/74320692954759008891869337523:ℝ),(25868278712252970884636995170349875200/74320692954759008891869337523:ℝ)]]
theorem admission37_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (49339826035028402108453741398525/202945038895128600280731204329472:ℝ) admission37_07_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission37_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_07_coefficients]
def admission37_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(18248858141128481353146731288053478705970313194141350821/5443410128522388346572461244360351562500000000:ℝ),(276516562523705331286842033174797966185520740858521544583/27217050642611941732862306221801757812500000000:ℝ),(279299546108366331287209962393291271752676404081913792853/27217050642611941732862306221801757812500000000:ℝ),(752218167173518307473212953564794508489964680427792019/217736405140895533862898449774414062500000000:ℝ)],
![(31647660248335592196467021764321958449059761709123407359/8709456205635821354515937990976562500000000000:ℝ),(479111612513085377176779124681036856000712866046760396619/43547281028179106772579689954882812500000000000:ℝ),(60438406046130748794400434220795724427933280700429594257/5443410128522388346572461244360351562500000000:ℝ),(20329241457394401431162647289817384420092732619231986779/5443410128522388346572461244360351562500000000:ℝ)]]
theorem admission37_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (18248858141128481353146731288053478705970313194141350821/7980123641418688768798800124161766195200000000000000000000:ℝ) admission37_08_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission37_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_08_coefficients]
def admission37_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5709457103691541814616861780939449182720347424/435472810281791067725796899548828125:ℝ),(85215133553312580699254975861876385607611025856/2177364051408955338628984497744140625:ℝ),(84788648349219986820012813406709080985233719296/2177364051408955338628984497744140625:ℝ),(5624160108021958143703653952762466938807386112/435472810281791067725796899548828125:ℝ)],
![(5574936729101232976428077209636547525574130942/435472810281791067725796899548828125:ℝ),(16640054521508754044153280213173286365969542132/435472810281791067725796899548828125:ℝ),(3311069168929847934388670067344761889117278208/87094562056358213545159379909765625:ℝ),(219609123898520310872861496807309694422482944/17418912411271642709031875981953125:ℝ)]]
theorem admission37_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (418871162220993634935114854445094479413/48706809334830864067375489039073280000000:ℝ) admission37_09_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission37_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_09_coefficients]
def admission37_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13218546223167635392430038530260992/2766730108491720703125:ℝ),(21897482305199853788300406930931712/1537072282495400390625:ℝ),(21764108717547865590995527458095104/1537072282495400390625:ℝ),(64892369292396283186406277395775488/13833650542458603515625:ℝ)],
![(2899332076591566805504526473314304/307414456499080078125:ℝ),(77802849261342513156242238547116032/2766730108491720703125:ℝ),(77323927420767028859086808874745856/2766730108491720703125:ℝ),(1707671135681157796825687239163904/184448673899448046875:ℝ)],
![(20599721952794354950927065388544/4426768173586753125:ℝ),(61416855925959113503245681079808/4426768173586753125:ℝ),(61034701036056768521898605993984/4426768173586753125:ℝ),(4043513442461214493915998060544/885353634717350625:ℝ)]]
theorem admission37_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1928097459059340712507247/845014423667944697364480000:ℝ) admission37_10_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission37_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_10_coefficients]
def admission37_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7128794238240753247585324701003257888/24773564318253002963956445841:ℝ),(42685792702182961597947387056768647168/74320692954759008891869337523:ℝ),(788868917457226173360878478490337280/2752618257583666995995160649:ℝ)],
![(7100462814217630371630109819996959950/24773564318253002963956445841:ℝ),(42515981536529355185480104192666961920/74320692954759008891869337523:ℝ),(2357182641224927687337354315952291840/8257854772751000987985481947:ℝ)]]
theorem admission37_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (8991938176059447049474160445985/45098897532250800062384712073216:ℝ) admission37_11_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission37_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_11_coefficients]
def admission37_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission37_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission37_12_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission37_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_12_coefficients]
def admission37_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission37_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission37_13_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission37_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_13_coefficients]
def admission37_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission37_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission37_14_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission37_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_14_coefficients]
theorem admission37_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission37_00_pos hδ hp
 · exact admission37_01_pos hδ hp
 · exact admission37_02_pos hδ hp
 · exact admission37_03_pos hδ hp
 · exact admission37_04_pos hδ hp
 · exact admission37_05_pos hδ hp
 · exact admission37_06_pos hδ hp
 · exact admission37_07_pos hδ hp
 · exact admission37_08_pos hδ hp
 · exact admission37_09_pos hδ hp
 · exact admission37_10_pos hδ hp
 · exact admission37_11_pos hδ hp
 · exact admission37_12_pos hδ hp
 · exact admission37_13_pos hδ hp
 · exact admission37_14_pos hδ hp
#print axioms admission37_all
end
end LewkoStage2Finite
