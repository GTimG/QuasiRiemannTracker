/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission42_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1202600869661870149/157406588190789:ℝ), (1202243463073679360/157406588190789:ℝ)]]
theorem admission42_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission42_00_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission42_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_00_coefficients]
def admission42_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(880074770458943488/157406588190789:ℝ), (879874770458943488/157406588190789:ℝ)]]
theorem admission42_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission42_01_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission42_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_01_coefficients]
def admission42_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(149254150863023530/52468862730263:ℝ), (149222075479105536/52468862730263:ℝ)]]
theorem admission42_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission42_02_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission42_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_02_coefficients]
def admission42_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(525850954450753498348355584/1416659293717101:ℝ), (16690123072738866842337280/22486655455827:ℝ), (525626808138995112718893056/1416659293717101:ℝ)],
![(525738544707211837000622080/1416659293717101:ℝ), (16686554559241148480020480/22486655455827:ℝ), (525514401533980517240668160/1416659293717101:ℝ)]]
theorem admission42_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (31323099227784902885/61894788982029287424:ℝ) admission42_03_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission42_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_03_coefficients]
def admission42_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3060663964719077685761784/52468862730263:ℝ), (6119176764510587602501632/52468862730263:ℝ), (3058512960296731042381824/52468862730263:ℝ)],
![(3061886821818401388545186/52468862730263:ℝ), (6121622048820160753917952/52468862730263:ℝ), (3059735387539055874932736/52468862730263:ℝ)]]
theorem admission42_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (68363091952280649/859649846972628992:ℝ) admission42_04_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission42_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_04_coefficients]
def admission42_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(161341821795223207641815599/4684719886630625:ℝ), (4065899952524484382356652522/59027470571545875:ℝ), (10164964555618840998612764873/295137352857729375:ℝ)],
![(32227948792515011140829749/936943977326125:ℝ), (580115443918304294687571526/8432495795935125:ℝ), (58012778477183951076736007/1686499159187025:ℝ)]]
theorem admission42_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (96683846377545033422489247/2060361595289534669520896000:ℝ) admission42_05_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission42_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_05_coefficients]
def admission42_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5664927690079687704724121214600907815357120512/8250685723952923479064059359493:ℝ), (5662713493022035546896071221505038568686747648/2750228574650974493021353119831:ℝ), (16981498928259904263413337337209922025487859712/8250685723952923479064059359493:ℝ), (5658286139228416070753115841764514134784737280/8250685723952923479064059359493:ℝ)],
![(5667017345219914756677779327256207461051432960/8250685723952923479064059359493:ℝ), (5664802869420496470685457028525390440713584640/2750228574650974493021353119831:ℝ), (16987766221368714305230792825178502729071329280/8250685723952923479064059359493:ℝ), (5660374958282061386510049613444538867982008320/8250685723952923479064059359493:ℝ)]]
theorem admission42_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10292362529486883560372217910779935/90119489934163132187323699030622208:ℝ) admission42_06_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission42_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_06_coefficients]
def admission42_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(490521521652672212548311874309777387448/2752981556207181674696049169:ℝ), (26481382385657498748833195814783859392512/74330502017593905216793327563:ℝ), (490270434217474483292808881450023649280/2752981556207181674696049169:ℝ)],
![(490282258698880491808672981038940411250/2752981556207181674696049169:ℝ), (26468463840475820365454862935510942720000/74330502017593905216793327563:ℝ), (490031232531086427545125836973670400000/2752981556207181674696049169:ℝ)]]
theorem admission42_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (43812206315793373663287684646875/180419399267593858232880278339584:ℝ) admission42_07_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission42_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_07_coefficients]
def admission42_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(50790837903967890963389304280745489646147595874141513093/3429156315030071242596123107910156250000000:ℝ), (4118809302393533985881099737153004495048537979551619147457/92587220505811923550095323913574218750000000:ℝ), (24246536273453721270355792799939615528431074203209297123481/544412856574174110474560504611816406250000000:ℝ), (28898182144533388043318660126046185646228191577876223321709/1944331630622050394552001802185058593750000000:ℝ)],
![(102565195712687913309480931576350997215532117329760295809/6858312630060142485192246215820312500000000:ℝ), (58220877253698832583837723934426449154832143202090362388733/1296221087081366929701334534790039062500000000:ℝ), (612016508652294864238763145498666667083280023704073625097969/13610321414354352761864012615295410156250000000:ℝ), (204237928366675187806144421793943485550346299384520943455483/13610321414354352761864012615295410156250000000:ℝ)]]
theorem admission42_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (152372513711903672890167912842236468938442787622424539279/61774188410258448160130831262108614656000000000000000000000:ℝ) admission42_08_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission42_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_08_coefficients]
def admission42_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(112141102707081979724759012750755737946552976696056/2177651426296696441898242018447265625:ℝ), (2490424188544852270126880378431215610161745688192/16130751305901455125172163099609375:ℝ), (335991237771340650004827603669425919331561592848384/2177651426296696441898242018447265625:ℝ), (22385015005335584904075343619086550252300170952704/435530285259339288379648403689453125:ℝ)],
![(22359599669785763368994358455770857481666738136762/435530285259339288379648403689453125:ℝ), (2482801041078547647305456043848309703542199866464/16130751305901455125172163099609375:ℝ), (66992460201415362557398741799770048679299684499456/435530285259339288379648403689453125:ℝ), (4463286352488496411378992414975936593120448217088/87106057051867857675929680737890625:ℝ)]]
theorem admission42_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (16627037348182858569096745606422188107373/1948529512090013668915107006067507200000000:ℝ) admission42_09_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission42_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_09_coefficients]
def admission42_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(294986746825728884909923473902831992832/1976366202172294921875:ℝ), (294754464318957947968758905390998421504/658788734057431640625:ℝ), (2061655355075581849869509796520873951232/4611521138402021484375:ℝ), (2060029542338661480759056693671478951936/13834563415206064453125:ℝ)],
![(117793462785977320275614465393205542912/395273240434458984375:ℝ), (823904058406364551406949902988600246272/922304227680404296875:ℝ), (493952346145295700983825766562761015296/553382536608242578125:ℝ), (91400421669022304757231153511160348672/307434742560134765625:ℝ)],
![(11759213701433943314697220804605120512/79054648086891796875:ℝ), (11749928400546537300081408865122185216/26351549362297265625:ℝ), (7044386141850532450618995455415549952/15810929617378359375:ℝ), (11731359209218094284735471486316314624/79054648086891796875:ℝ)]]
theorem admission42_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (10925679662467999648987754701/4828972488959846881689600000000:ℝ) admission42_10_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission42_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_10_coefficients]
def admission42_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3620411098773965013475010746938557797000/24776834005864635072264442521:ℝ), (7238974180867733060918581281418495459328/24776834005864635072264442521:ℝ), (10855689651282652192701043525574490849280/74330502017593905216793327563:ℝ)],
![(3618600879388095387358667632424311103230/24776834005864635072264442521:ℝ), (7235354214648765537583950696578640035840/24776834005864635072264442521:ℝ), (10850260410676618747806288754498884075520/74330502017593905216793327563:ℝ)]]
theorem admission42_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (646725917498863860834019705921345/3247549186816689448191845010112512:ℝ) admission42_11_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission42_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_11_coefficients]
def admission42_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission42_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission42_12_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission42_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_12_coefficients]
def admission42_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission42_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission42_13_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission42_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_13_coefficients]
def admission42_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission42_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission42_14_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission42_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_14_coefficients]
theorem admission42_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission42_00_pos hδ hp
 · exact admission42_01_pos hδ hp
 · exact admission42_02_pos hδ hp
 · exact admission42_03_pos hδ hp
 · exact admission42_04_pos hδ hp
 · exact admission42_05_pos hδ hp
 · exact admission42_06_pos hδ hp
 · exact admission42_07_pos hδ hp
 · exact admission42_08_pos hδ hp
 · exact admission42_09_pos hδ hp
 · exact admission42_10_pos hδ hp
 · exact admission42_11_pos hδ hp
 · exact admission42_12_pos hδ hp
 · exact admission42_13_pos hδ hp
 · exact admission42_14_pos hδ hp
#print axioms admission42_all
end
end Record1252270103Finite
