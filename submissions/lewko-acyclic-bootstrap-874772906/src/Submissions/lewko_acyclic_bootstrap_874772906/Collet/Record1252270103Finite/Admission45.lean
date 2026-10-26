/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission45_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(114516396796930929/7495551818609:ℝ), (2404486926147358720/157406588190789:ℝ)]]
theorem admission45_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission45_00_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission45_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_00_coefficients]
def admission45_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(83807120996089856/7495551818609:ℝ), (1759749540917886976/157406588190789:ℝ)]]
theorem admission45_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission45_01_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission45_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_01_coefficients]
def admission45_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(42639460906018438/7495551818609:ℝ), (298444150958211072/52468862730263:ℝ)]]
theorem admission45_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission45_02_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission45_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_02_coefficients]
def admission45_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(467223528963101698358460416/157406588190789:ℝ), (1201303850702851346164498432/202379899102443:ℝ), (4204115212271844137925345280/1416659293717101:ℝ)],
![(467173569774333641286025216/157406588190789:ℝ), (8408227695799188527586672640/1416659293717101:ℝ), (4203665585851785756012445696/1416659293717101:ℝ)]]
theorem admission45_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15659874624951875791/30947394491014643712:ℝ) admission45_03_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission45_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_03_coefficients]
def admission45_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24484044521552508726236910/52468862730263:ℝ), (48959482446273637657559040/52468862730263:ℝ), (24475438245827797334360064/52468862730263:ℝ)],
![(24488935090203730412987544/52468862730263:ℝ), (48969262723862083290595328/52468862730263:ℝ), (24480327954797096664563712/52468862730263:ℝ)]]
theorem admission45_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (547068675886715889/6877198775781031936:ℝ) admission45_04_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission45_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_04_coefficients]
def admission45_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2320437031967399551408590266/8432495795935125:ℝ), (162432326855868188338649136088/295137352857729375:ℝ), (27072343289646677257420032676/98379117619243125:ℝ)],
![(84988877139066732533325052/309044348542125:ℝ), (162330495116458046902476763096/295137352857729375:ℝ), (27055372193497811177174747812/98379117619243125:ℝ)]]
theorem admission45_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (21247219284766683133331263/453063806294033801674752000:ℝ) admission45_05_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission45_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_05_coefficients]
def admission45_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(90610782334118681112762985236115504660679360512/8250685723952923479064059359493:ℝ), (271779204562597054965490545948662865587494518784/8250685723952923479064059359493:ℝ), (271726066284866940307190944755650683881738207232/8250685723952923479064059359493:ℝ), (90557644056298400921133058728392522954923048960/8250685723952923479064059359493:ℝ)],
![(90627496230616746293659190029480465359234924544/8250685723952923479064059359493:ℝ), (271829342907744932570038285372739448033173045248/8250685723952923479064059359493:ℝ), (271776201285945924263543971967685303494439337984/8250685723952923479064059359493:ℝ), (90574354608727563447188528901832720820501217280/8250685723952923479064059359493:ℝ)]]
theorem admission45_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (82361697474242101562716069318769335/720955919473305057498589592244977664:ℝ) admission45_06_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission45_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_06_coefficients]
def admission45_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(105873852899033232048228605648701967409322/74330502017593905216793327563:ℝ), (211720598280384503065559735573256894857216/74330502017593905216793327563:ℝ), (3920249860248691420361006695789363200000/2752981556207181674696049169:ℝ)],
![(105848015808566699699692580450254914648904/74330502017593905216793327563:ℝ), (30238418201127319468293328715894987227136/10618643145370557888113332509:ℝ), (3919293053503139197370274517883950202880/2752981556207181674696049169:ℝ)]]
theorem admission45_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (21900756583566623911467983487345/90209699633796929116440139169792:ℝ) admission45_07_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission45_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_07_coefficients]
def admission45_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1300651944507342603786468172012789329155529956380383803596183/5444128565741741104745605046118164062500000000:ℝ), (19520926792093812204544478930340858249862906349687231216109017/27220642828708705523728025230590820312500000000:ℝ), (19532074248994659448061444094043178184971895323501348819207207/27220642828708705523728025230590820312500000000:ℝ), (1302881435876622086077810042003418203447865797723182910153321/5444128565741741104745605046118164062500000000:ℝ)],
![(26671344125732397260275100052381596316002800958028494025937/111104664606974308260114388696289062500000000:ℝ), (2802082345961239643891641272154522133511189840180293216608697/3888663261244100789104003604370117187500000000:ℝ), (19625714744040869423970321919923472880593895672637375520179239/27220642828708705523728025230590820312500000000:ℝ), (261824705322486958977426840984120559746692492881844505360917/1088825713148348220949121009223632812500000000:ℝ)]]
theorem admission45_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1300651944507342603786468172012789329155529956380383803596183/523054408107340332261459774462526062015283200000000000000000000:ℝ) admission45_08_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission45_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_08_coefficients]
def admission45_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(357408088979706884015630741775864088477917400843894/435530285259339288379648403689453125:ℝ), (5359395370973000814467707850120600922296193407777984/2177651426296696441898242018447265625:ℝ), (5357669467066243171082832434946473236505879420862464/2177651426296696441898242018447265625:ℝ), (71412581639815942582063878639614985489927171473408/87106057051867857675929680737890625:ℝ)],
![(356859272530740156332747680169423336417835242517304/435530285259339288379648403689453125:ℝ), (5351163876813250132019176254774707605167725458489088/2177651426296696441898242018447265625:ℝ), (5349438725435601651380673963611758495563750947422208/2177651426296696441898242018447265625:ℝ), (356514242255934890132876340844419989156052418428928/435530285259339288379648403689453125:ℝ)]]
theorem admission45_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (41503720248110463159726506663069593389059/4871323780225034172287767515168768000000000:ℝ) admission45_09_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission45_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_09_coefficients]
def admission45_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(65773589541488248150921314626348812673024/13834563415206064453125:ℝ), (4383173361121283739845194061074518237184/307434742560134765625:ℝ), (21907203983300495515683260842130991480832/1537173712800673828125:ℝ), (9385089162979247694631391708167773618176/1976366202172294921875:ℝ)],
![(14603826300923665892080876825456853450752/1537173712800673828125:ℝ), (394147400584538151128591438992108716752896/13834563415206064453125:ℝ), (56284499284164781428414362572153667190784/1976366202172294921875:ℝ), (8751902074211194970556632696138575642624/922304227680404296875:ℝ)],
![(65660834594295554847200845139454325817344/13834563415206064453125:ℝ), (196904561619788765549414761259474137513984/13834563415206064453125:ℝ), (196826621428453177233117562971120977575936/13834563415206064453125:ℝ), (65582894403079784828028646851101165879296/13834563415206064453125:ℝ)]]
theorem admission45_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (477178359892275947117222290043/211267546391993301073920000000000:ℝ) admission45_10_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission45_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_10_coefficients]
def admission45_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(86824248550577991931599630698179988954966/74330502017593905216793327563:ℝ), (173626331026308465073028953970198047588352/74330502017593905216793327563:ℝ), (86802083285412949982450310035991072604160/74330502017593905216793327563:ℝ)],
![(86802528753157447038351954829042075829432/74330502017593905216793327563:ℝ), (3542508046256541350070247987282785468416/1516949020767222555444761787:ℝ), (86780366322988816202871290951688645509120/74330502017593905216793327563:ℝ)]]
theorem admission45_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (323282056760001242916551571159395/1623774593408344724095922505056256:ℝ) admission45_11_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission45_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_11_coefficients]
def admission45_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission45_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission45_12_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission45_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_12_coefficients]
def admission45_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission45_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission45_13_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission45_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_13_coefficients]
def admission45_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission45_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission45_14_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission45_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_14_coefficients]
theorem admission45_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission45_00_pos hδ hp
 · exact admission45_01_pos hδ hp
 · exact admission45_02_pos hδ hp
 · exact admission45_03_pos hδ hp
 · exact admission45_04_pos hδ hp
 · exact admission45_05_pos hδ hp
 · exact admission45_06_pos hδ hp
 · exact admission45_07_pos hδ hp
 · exact admission45_08_pos hδ hp
 · exact admission45_09_pos hδ hp
 · exact admission45_10_pos hδ hp
 · exact admission45_11_pos hδ hp
 · exact admission45_12_pos hδ hp
 · exact admission45_13_pos hδ hp
 · exact admission45_14_pos hδ hp
#print axioms admission45_all
end
end Record1252270103Finite
