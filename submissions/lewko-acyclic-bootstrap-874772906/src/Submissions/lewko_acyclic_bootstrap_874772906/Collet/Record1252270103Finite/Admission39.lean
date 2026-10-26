/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission39_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(42988324622372947/22486655455827:ℝ), (300560865768419840/157406588190789:ℝ)]]
theorem admission39_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission39_00_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission39_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_00_coefficients]
def admission39_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31452670373533696/22486655455827:ℝ), (219968692614735872/157406588190789:ℝ)]]
theorem admission39_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission39_01_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission39_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_01_coefficients]
def admission39_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(5333942036242054/7495551818609:ℝ), (37305518869776384/52468862730263:ℝ)]]
theorem admission39_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission39_02_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission39_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_02_coefficients]
def admission39_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8233077730000199895666688/1416659293717101:ℝ), (783435313970654010576896/67459966367481:ℝ), (8219066113383534326448128/1416659293717101:ℝ)],
![(8226051533905021210900480/1416659293717101:ℝ), (5479363327558381106653184/472219764572367:ℝ), (1173148671510017444151296/202379899102443:ℝ)]]
theorem admission39_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1118801757345216221/2210528177929617408:ℝ) admission39_03_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission39_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_03_coefficients]
def admission39_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(47885424536133142292500/52468862730263:ℝ), (95636448595217016320000/52468862730263:ℝ), (47751064153313771520000/52468862730263:ℝ)],
![(6851704818154957117650/7495551818609:ℝ), (95789359456738491967488/52468862730263:ℝ), (47827465855959073554432/52468862730263:ℝ)]]
theorem admission39_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (34154222598061875/429824923486314496:ℝ) admission39_04_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission39_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_04_coefficients]
def admission39_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(53169149157789375093919889/98379117619243125:ℝ), (319041300699408233356703054/295137352857729375:ℝ), (159533744836621934679630887/295137352857729375:ℝ)],
![(52903760646686791297987571/98379117619243125:ℝ), (317449615120833918996124622/295137352857729375:ℝ), (158738224704643837168133159/295137352857729375:ℝ)]]
theorem admission39_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (52903760646686791297987571/1126760247423964272394240000:ℝ) admission39_05_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission39_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_05_coefficients]
def admission39_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22190132054546560296696839339612991780208640/8250685723952923479064059359493:ℝ), (2461724460714219079735511784224431373434880/305580952738997165891261457759:ℝ), (66362789728500058631200146000089095413432320/8250685723952923479064059359493:ℝ), (22086361332504396247028313665642440110899200/8250685723952923479064059359493:ℝ)],
![(600616814423934180043220628484787482763264/222991506052781715650379982689:ℝ), (117397845433126031566682187616607092727808/14551473939952245994821974179:ℝ), (66460755368381813716472302355621911281532928/8250685723952923479064059359493:ℝ), (3159857018602514900818629121163260938158080/1178669389136131925580579908499:ℝ)]]
theorem admission39_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5142381725018936266896387949968325/45059744967081566093661849515311104:ℝ) admission39_06_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission39_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_06_coefficients]
def admission39_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9886201839840173173448783939184635020/3539547715123519296037777503:ℝ), (2171707688481188253130318677279109120/389164932029287461868027893:ℝ), (7673556876872385600151555267457187840/2752981556207181674696049169:ℝ)],
![(69068724052835789179329255293450503006/24776834005864635072264442521:ℝ), (59141207039880917849799781837879617536/10618643145370557888113332509:ℝ), (7658606771473132115921364987685109760/2752981556207181674696049169:ℝ)]]
theorem admission39_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (10955724866113374875909850579765/45104849816898464558220069584896:ℝ) admission39_07_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission39_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_07_coefficients]
def admission39_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(136549030918487102448352155062848699066644553786406584487/2419612695885218268775824464941406250000000000:ℝ), (411600311291180657273192635142355309668251203448881934073/2419612695885218268775824464941406250000000000:ℝ), (3721979608231960811610640331674301608640113155420879560291/21776514262966964418982420184472656250000000000:ℝ), (1246518079438718512497752891472620482288707239122663914017/21776514262966964418982420184472656250000000000:ℝ)],
![(354950512561281113576926340883590609537802005367203598107/6049031739713045671939561162353515625000000000:ℝ), (66856427281776357192957118255442329392515187273715572911/378064483732065354496222572647094726562500000:ℝ), (19341963924826564857209338382886938199359571957214193577967/108882571314834822094912100922363281250000000000:ℝ), (259056882662451060014119582852625026591486239521469683821/4355302852593392883796484036894531250000000000:ℝ)]]
theorem admission39_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (136549030918487102448352155062848699066644553786406584487/56755035601924949247120201222062289715200000000000000000000:ℝ) admission39_08_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission39_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_08_coefficients]
def admission39_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(89056705996594975431990500457235122209337351956/435530285259339288379648403689453125:ℝ), (88830783345085963488795847039866383241113212784/145176761753113096126549467896484375:ℝ), (265814770336738977324172442975962589592099651584/435530285259339288379648403689453125:ℝ), (88379126388521269020338589936760100608370802688/435530285259339288379648403689453125:ℝ)],
![(439913700872385441281497474516491087461827688758/2177651426296696441898242018447265625:ℝ), (438788010603269523508486531693146397659089925448/725883808765565480632747339482421875:ℝ), (1312987896576417999929949571239286762978532048896/2177651426296696441898242018447265625:ℝ), (12472501888330933861877875472646828464816521216/62218612179905612625664057669921875:ℝ)]]
theorem admission39_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2973676178057416406125515812074381939129/347951698587502440877697679654912000000000:ℝ) admission39_09_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission39_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_09_coefficients]
def admission39_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(97851936834969280811024190314180608/658788734057431640625:ℝ), (2048520874032515401763695606991392768/4611521138402021484375:ℝ), (6126457104697839007734700652154978304/13834563415206064453125:ℝ), (2035785158002323480725121827778592768/13834563415206064453125:ℝ)],
![(1360760302731311167136418500471468032/4611521138402021484375:ℝ), (4069557686749088548666554419484798976/4611521138402021484375:ℝ), (12170511134874665123456237953465581568/13834563415206064453125:ℝ), (4044118986559672822615830196425588736/13834563415206064453125:ℝ)],
![(45052569641344644142449921390705664/307434742560134765625:ℝ), (32079559192003528211791572708195328/73198748228603515625:ℝ), (671553370092316232661358891043618816/1537173712800673828125:ℝ), (223145475474817056238485471125045248/1537173712800673828125:ℝ)]]
theorem admission39_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (39901520396736333889690423809/17605628865999441756160000000000:ℝ) admission39_10_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission39_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_10_coefficients]
def admission39_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8107808124647047869014769043999687540/3539547715123519296037777503:ℝ), (197894666467391002876946198907412480/43240548003254162429780877:ℝ), (169917062396933894528635706630298664960/74330502017593905216793327563:ℝ)],
![(56641429537254080549966687846966416546/24776834005864635072264442521:ℝ), (1796306466775037213121855113467211776/393283079458168810670864167:ℝ), (169577734859056804222713533438073241600/74330502017593905216793327563:ℝ)]]
theorem admission39_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (161721930369431308958734067380975/811887296704172362047961252528128:ℝ) admission39_11_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission39_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_11_coefficients]
def admission39_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission39_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission39_12_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission39_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_12_coefficients]
def admission39_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission39_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission39_13_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission39_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_13_coefficients]
def admission39_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission39_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission39_14_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission39_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_14_coefficients]
theorem admission39_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission39_00_pos hδ hp
 · exact admission39_01_pos hδ hp
 · exact admission39_02_pos hδ hp
 · exact admission39_03_pos hδ hp
 · exact admission39_04_pos hδ hp
 · exact admission39_05_pos hδ hp
 · exact admission39_06_pos hδ hp
 · exact admission39_07_pos hδ hp
 · exact admission39_08_pos hδ hp
 · exact admission39_09_pos hδ hp
 · exact admission39_10_pos hδ hp
 · exact admission39_11_pos hδ hp
 · exact admission39_12_pos hδ hp
 · exact admission39_13_pos hδ hp
 · exact admission39_14_pos hδ hp
#print axioms admission39_all
end
end Record1252270103Finite
