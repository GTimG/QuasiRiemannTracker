/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission24_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19142460698717029/157406588190789:ℝ), (18785054110526240/157406588190789:ℝ)]]
theorem admission24_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission24_00_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission24_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_00_coefficients]
def admission24_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13948043288420992/157406588190789:ℝ), (13748043288420992/157406588190789:ℝ)]]
theorem admission24_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission24_01_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission24_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_01_coefficients]
def admission24_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363670313279018/52468862730263:ℝ), (2331594929361024/52468862730263:ℝ)]]
theorem admission24_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission24_02_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission24_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_02_coefficients]
def admission24_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4097087486312400042368/1416659293717101:ℝ), (898254370206745767296/157406588190789:ℝ), (3987488045548311863296/1416659293717101:ℝ)],
![(4069597199899604357120/1416659293717101:ℝ), (892150469627280527360/157406588190789:ℝ), (3960045026745920389120/1416659293717101:ℝ)]]
theorem admission24_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (30212745870559085/60444129865262976:ℝ) admission24_03_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission24_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_03_coefficients]
def admission24_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24799256281507053846/52468862730263:ℝ), (48520466296641873024/52468862730263:ℝ), (23726310001177780224/52468862730263:ℝ)],
![(25104448522278656576/52468862730263:ℝ), (7017724373283966976/7495551818609:ℝ), (3432107736019427328/7495551818609:ℝ)]]
theorem admission24_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8688834228946941/107456230871578624:ℝ) admission24_04_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission24_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_04_coefficients]
def admission24_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1187825956442087750318/4684719886630625:ℝ), (150009159587766535724632/295137352857729375:ℝ), (75162337197923351570848/295137352857729375:ℝ)],
![(1191475373807780064/4905465849875:ℝ), (28750765278611038063424/59027470571545875:ℝ), (14410967336476781633312/59027470571545875:ℝ)]]
theorem admission24_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (111700816294479381/2571876879499264000:ℝ) admission24_05_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission24_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_05_coefficients]
def admission24_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(736692404104945911710796130952275466752/8250685723952923479064059359493:ℝ), (719282293048052109671000087173146910208/2750228574650974493021353119831:ℝ), (2106134456514558500564239547643175124992/8250685723952923479064059359493:ℝ), (684978549418630520408670217076009861120/8250685723952923479064059359493:ℝ)],
![(744866881446538922500737916544324976640/8250685723952923479064059359493:ℝ), (727387286993401517912476885553055088640/2750228574650974493021353119831:ℝ), (2130243182347985923113175943152858562560/8250685723952923479064059359493:ℝ), (692946761750956706615235203038018273280/8250685723952923479064059359493:ℝ)]]
theorem admission24_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1306492899739514389817562517311115/11264936241770391523415462378827776:ℝ) admission24_06_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission24_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_06_coefficients]
def admission24_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1633999397809413300433310552122334/1179849238374506432012592501:ℝ), (28945122124269285716155205317446784/10618643145370557888113332509:ℝ), (3692105022645500228723207113850880/2752981556207181674696049169:ℝ)],
![(1608559434663191102763068583782720/1179849238374506432012592501:ℝ), (28490924491203895000628316195205120/10618643145370557888113332509:ℝ), (519100881918523757992718047641600/393283079458168810670864167:ℝ)]]
theorem admission24_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (5940638144514355750954262325/25170117085322803882935306688:ℝ) admission24_07_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission24_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_07_coefficients]
def admission24_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6102788908116153452430878572668809277981647558212943/2633592049943094714313822546875000000000000000:ℝ), (1209555710140805647072814485862671937381478466778026127/165916299146414967001770820453125000000000000000:ℝ), (26578576073231578026170623318634613854629824524749397809/3484242282074714307037187229515625000000000000000:ℝ), (188811942677104266655172320114528673789022312590338219/71106985348463557286473208765625000000000000000:ℝ)],
![(7597025260779579155376478576775356189945419455716337/2633592049943094714313822546875000000000000000:ℝ), (1488513009079632209040664950098391849482020512347263853/165916299146414967001770820453125000000000000000:ℝ), (32364740269500293515296072259129427120889263764614388273/3484242282074714307037187229515625000000000000000:ℝ), (11156720108113139830667702388365992932409122945234561211/3484242282074714307037187229515625000000000000000:ℝ)]]
theorem admission24_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6102788908116153452430878572668809277981647558212943/1885198620918531743168055153262592000000000000000000000:ℝ) admission24_08_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission24_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_08_coefficients]
def admission24_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(27586063977392183575990087758327843197693059/4355302852593392883796484036894531250:ℝ), (8853114609494448802746452763401816052799903/483922539177043653755164892988281250:ℝ), (38305146752725863189043429709813985199369664/2177651426296696441898242018447265625:ℝ), (2451844104369683200573352896881647962904576/435530285259339288379648403689453125:ℝ)],
![(2487725114551570668551084808800776338799312/435530285259339288379648403689453125:ℝ), (796054192247347508322277977176083708627216/48392253917704365375516489298828125:ℝ), (6866970833925763949523850400158541428836352/435530285259339288379648403689453125:ℝ), (438043959047533711052489835810299252998144/87106057051867857675929680737890625:ℝ)]]
theorem admission24_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (13368040742417410615615534540109230133/1902860851650403973549909185612800000000:ℝ) admission24_09_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission24_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_09_coefficients]
def admission24_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8078978702898957386372204779072/13834563415206064453125:ℝ), (7710671962164240008157495927616/4611521138402021484375:ℝ), (489562029916848112258019471744/307434742560134765625:ℝ), (6977284381359714913510593224704/13834563415206064453125:ℝ)],
![(3052396362656667760266945753088/2766912683041212890625:ℝ), (16610117312445749735109185536/5270309872459453125:ℝ), (8284674371934964162350527553536/2766912683041212890625:ℝ), (872257103019204437228383633408/922304227680404296875:ℝ)],
![(287072286629529590932349452288/553382536608242578125:ℝ), (38954586689032747255452073984/26351549362297265625:ℝ), (774995957295770333787938750464/553382536608242578125:ℝ), (244023147455612232355794649088/553382536608242578125:ℝ)]]
theorem admission24_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (58179652084258134926747/32236869261473587200000000:ℝ) admission24_10_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission24_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_10_coefficients]
def admission24_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4018359997858890964929443067067622/3539547715123519296037777503:ℝ), (7909421186695709956612485340915456/3539547715123519296037777503:ℝ), (81724661065847518180771195160453120/74330502017593905216793327563:ℝ)],
![(3954181306899694429234649920961600/3539547715123519296037777503:ℝ), (7782128616923220844005864087592960/3539547715123519296037777503:ℝ), (1640799242265614983127810329149440/1516949020767222555444761787:ℝ)]]
theorem admission24_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12518304765820426812193377145/64723158219401495698976502912:ℝ) admission24_11_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
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
def admission24_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission24_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission24_13_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
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
end Record1252270103Finite
