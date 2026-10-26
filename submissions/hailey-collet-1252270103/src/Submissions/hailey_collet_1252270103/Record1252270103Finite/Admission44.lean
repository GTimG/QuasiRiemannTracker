/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission44_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(114516396796930929/7495551818609:ℝ), (2404486926147358720/157406588190789:ℝ)]]
theorem admission44_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission44_00_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission44_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_00_coefficients]
def admission44_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(83807120996089856/7495551818609:ℝ), (1759749540917886976/157406588190789:ℝ)]]
theorem admission44_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission44_01_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission44_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_01_coefficients]
def admission44_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(42639460906018438/7495551818609:ℝ), (298444150958211072/52468862730263:ℝ)]]
theorem admission44_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission44_02_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission44_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_02_coefficients]
def admission44_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(467248508906310956435734528/157406588190789:ℝ), (1201368083945810276686200832/202379899102443:ℝ), (4204340025481873328881795072/1416659293717101:ℝ)],
![(155732849905847633121099776/52468862730263:ℝ), (8408677328499901041238589440/1416659293717101:ℝ), (4203890399061814946968895488/1416659293717101:ℝ)]]
theorem admission44_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (62642848477688654467/123789577964058574848:ℝ) admission44_03_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission44_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_03_coefficients]
def admission44_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3497371258197990957798300/7495551818609:ℝ), (6993513125379213050675200/7495551818609:ℝ), (3496141913049021095608320/7495551818609:ℝ)],
![(24486489376037158391338734/52468862730263:ℝ), (48964372155242936987762688/52468862730263:ℝ), (24477883100312446999461888/52468862730263:ℝ)]]
theorem admission44_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (39072430652182785/491228483984359424:ℝ) admission44_04_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission44_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_04_coefficients]
def admission44_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16248151068876822332857655327/59027470571545875:ℝ), (32496648028845615008969254886/59027470571545875:ℝ), (5416165595457433509867222353/19675823523848625:ℝ)],
![(16237967378666771386862608397/59027470571545875:ℝ), (162381408404817933608673901438/295137352857729375:ℝ), (27063856881138301469090826901/98379117619243125:ℝ)]]
theorem admission44_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (16237967378666771386862608397/346140748008641824479510528000:ℝ) admission44_05_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission44_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_05_coefficients]
def admission44_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(90602423713835197194894515529470642894912880640/8250685723952923479064059359493:ℝ), (271754132046092921150026011784746579940183244800/8250685723952923479064059359493:ℝ), (271700997112431700139921122803776361067404328960/8250685723952923479064059359493:ℝ), (90549288780083819658105323641672424022133964800/8250685723952923479064059359493:ℝ)],
![(12945591087190466053684388617547943370495492096/1178669389136131925580579908499:ℝ), (271804270391240798754573751208823162385861771264/8250685723952923479064059359493:ℝ), (271751132113510684096274150015810980680105459712/8250685723952923479064059359493:ℝ), (90565999332512982184160793815112621887712133120/8250685723952923479064059359493:ℝ)]]
theorem admission44_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41177049197396545268068313653963025/360477959736652528749294796122488832:ℝ) admission44_06_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission44_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_06_coefficients]
def admission44_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(554381010986569682651255216991758872820/389164932029287461868027893:ℝ), (211746435370747859832316401331802728202240/74330502017593905216793327563:ℝ), (560104037660209647408053254963152814080/393283079458168810670864167:ℝ)],
![(105860936007968277037853721246978891948202/74330502017593905216793327563:ℝ), (30242109214036370434972852395687249133568/10618643145370557888113332509:ℝ), (3919771456875915308865640606836656701440/2752981556207181674696049169:ℝ)]]
theorem admission44_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (87613719482926621486223651621565/360838798535187716465760556679168:ℝ) admission44_07_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission44_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_07_coefficients]
def admission44_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(648764992840285086401481153367917441995613155549438800879409/2722064282870870552372802523059082031250000000:ℝ), (278201522069436190951429384782205403465886264247642899193109/388866326124410078910400360437011718750000000:ℝ), (389705262727000718738103084946344003336288993071758302915913/544412856574174110474560504611816406250000000:ℝ), (13262870448648793961755017799624367891087477309373974442239/55552332303487154130057194348144531250000000:ℝ)],
![(325943475833528758692493509322435943579958400415472501358387/1361032141435435276186401261529541015625000000:ℝ), (4891939043623849667324266727373793731831865257227456060917373/6805160707177176380932006307647705078125000000:ℝ), (9789451815698122956407016036598747431218225001361970923383841/13610321414354352761864012615295410156250000000:ℝ), (653001697351697258530657953640186324306084721502344555995343/2722064282870870552372802523059082031250000000:ℝ)]]
theorem admission44_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (648764992840285086401481153367917441995613155549438800879409/261527204053670166130729887231263031007641600000000000000000000:ℝ) admission44_08_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission44_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_08_coefficients]
def admission44_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(357682572457101200309792277205477371391207839701428/435530285259339288379648403689453125:ℝ), (1072702374111833065217083310562816440444557113006208/435530285259339288379648403689453125:ℝ), (1072357042824659703990833602725755188049226420453376/435530285259339288379648403689453125:ℝ), (357337241170652124299040919374902396596427576836096/435530285259339288379648403689453125:ℝ)],
![(51019108001162067518129887942719517047303668767834/62218612179905612625664057669921875:ℝ), (5355280376399414643636884957468188885094317615742144/2177651426296696441898242018447265625:ℝ), (5353554472492657000252009542294061199304003628826624/2177651426296696441898242018447265625:ℝ), (356788575227507301521597867021247458302844137897984/435530285259339288379648403689453125:ℝ)]]
theorem admission44_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (166142627237135219164936741358250127314983/19485295120900136689151070060675072000000000:ℝ) admission44_09_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission44_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_09_coefficients]
def admission44_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(65829954474735086876234773233589589671936/13834563415206064453125:ℝ), (197411870845881112912780171609560112529408/13834563415206064453125:ℝ), (197333880242301652248327234618575456043008/13834563415206064453125:ℝ), (65751963871275396643813086242604933185536/13834563415206064453125:ℝ)],
![(18792455959980721505795181710030045741056/1976366202172294921875:ℝ), (394485615203968074940370206683084817596416/13834563415206064453125:ℝ), (394329659196339521462523566993420274630656/13834563415206064453125:ℝ), (18770176530353723122419768897220825317376/1976366202172294921875:ℝ)],
![(21905741557533591211241922357770729316352/4611521138402021484375:ℝ), (65691235547931781580482363363081148833792/4611521138402021484375:ℝ), (9380749583002001718550604996193764245504/658788734057431640625:ℝ), (21879753090655753115074731468045930201088/4611521138402021484375:ℝ)]]
theorem admission44_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2547138497542561161689778262289/1126760247423964272394240000000000:ℝ) admission44_10_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission44_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_10_coefficients]
def admission44_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(454634083072180470864176947775741824780/389164932029287461868027893:ℝ), (173648050823622270213036737479237180129280/74330502017593905216793327563:ℝ), (12401848823803573838891402796877469450240/10618643145370557888113332509:ℝ)],
![(86813390069365925041810121156028775407446/74330502017593905216793327563:ℝ), (24800659151983475899064276412270802927616/10618643145370557888113332509:ℝ), (86791224804200883092660800493839859056640/74330502017593905216793327563:ℝ)]]
theorem admission44_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1293290031018866346667122848240135/6495098373633378896383690020225024:ℝ) admission44_11_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission44_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_11_coefficients]
def admission44_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission44_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission44_12_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission44_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_12_coefficients]
def admission44_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission44_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission44_13_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission44_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_13_coefficients]
def admission44_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission44_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission44_14_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission44_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_14_coefficients]
theorem admission44_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission44_00_pos hδ hp
 · exact admission44_01_pos hδ hp
 · exact admission44_02_pos hδ hp
 · exact admission44_03_pos hδ hp
 · exact admission44_04_pos hδ hp
 · exact admission44_05_pos hδ hp
 · exact admission44_06_pos hδ hp
 · exact admission44_07_pos hδ hp
 · exact admission44_08_pos hδ hp
 · exact admission44_09_pos hδ hp
 · exact admission44_10_pos hδ hp
 · exact admission44_11_pos hδ hp
 · exact admission44_12_pos hδ hp
 · exact admission44_13_pos hδ hp
 · exact admission44_14_pos hδ hp
#print axioms admission44_all
end
end Record1252270103Finite
