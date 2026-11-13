/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission032_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(86792527054547090758185254912/1418317983:ℝ),(260351814024674163712279445504/1418317983:ℝ),(260326046885707055150003126272/1418317983:ℝ),(86766759915579982195908935680/1418317983:ℝ)],
![(173585054109094181516370509824/1418317983:ℝ),(520703628049348327424558891008/1418317983:ℝ),(520652093771414110300006252544/1418317983:ℝ),(173533519831159964391817871360/1418317983:ℝ)],
![(86792527054547090758185254912/1418317983:ℝ),(260351814024674163712279445504/1418317983:ℝ),(260326046885707055150003126272/1418317983:ℝ),(86766759915579982195908935680/1418317983:ℝ)]]
theorem admission032_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission032_00_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission032_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_00_coefficients]
def admission032_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(63524861347684514826807148544/1418317983:ℝ),(190560172524245958893221445632/1418317983:ℝ),(190545761005438373306021445632/1418317983:ℝ),(7056716647652992137734127616/157590887:ℝ)],
![(127049722695369029653614297088/1418317983:ℝ),(381120345048491917786442891264/1418317983:ℝ),(381091522010876746612042891264/1418317983:ℝ),(14113433295305984275468255232/157590887:ℝ)],
![(63524861347684514826807148544/1418317983:ℝ),(190560172524245958893221445632/1418317983:ℝ),(190545761005438373306021445632/1418317983:ℝ),(7056716647652992137734127616/157590887:ℝ)]]
theorem admission032_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission032_01_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission032_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_01_coefficients]
def admission032_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(504909270897048267959702348890112/22161218484375:ℝ),(504873144790662919948478651039744/7387072828125:ℝ),(504837018684277571937254953189376/7387072828125:ℝ),(504800892577892223926031255339008/22161218484375:ℝ)],
![(1009818541794096535919404697780224/22161218484375:ℝ),(1009746289581325839896957302079488/7387072828125:ℝ),(1009674037368555143874509906378752/7387072828125:ℝ),(1009601785155784447852062510678016/22161218484375:ℝ)],
![(504909270897048267959702348890112/22161218484375:ℝ),(504873144790662919948478651039744/7387072828125:ℝ),(504837018684277571937254953189376/7387072828125:ℝ),(504800892577892223926031255339008/22161218484375:ℝ)]]
theorem admission032_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission032_02_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission032_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_02_coefficients]
def admission032_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141369834969680430482843500544/4254953949:ℝ),(424049283059749676848850665472/4254953949:ℝ),(423989063628793085353170829312/4254953949:ℝ),(141309615538723838987163664384/4254953949:ℝ)],
![(282709450361807290029410615296/4254953949:ℝ),(848007908225199904856265981952/4254953949:ℝ),(847887470202131169653100118016/4254953949:ℝ),(282589012338738554826244751360/4254953949:ℝ)],
![(141339615392126859546567114752/4254953949:ℝ),(423958625165450228007415316480/4254953949:ℝ),(423898406573338084299929288704/4254953949:ℝ),(141279396800014715839081086976/4254953949:ℝ)]]
theorem admission032_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (15685163923253/30983629111296:ℝ) admission032_03_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission032_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_03_coefficients]
def admission032_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2571924529772925415015321698304/492471521875:ℝ),(23141899763239297948598526803968/1477414565625:ℝ),(23136479162666708778594634563584/1477414565625:ℝ),(7710352988746187075042072854528/1477414565625:ℝ)],
![(15434629321809993042203835891712/1477414565625:ℝ),(77155074788130153288260065951744/2462357609375:ℝ),(77137004314493060320924413198336/2462357609375:ℝ),(77118935188138686309012221198336/7387072828125:ℝ)],
![(308754229299648671886314831872/59096582625:ℝ),(115755725548193970121787563835392/7387072828125:ℝ),(115728617130145637069800066777088/7387072828125:ℝ),(12855723414802583644600618975232/2462357609375:ℝ)]]
theorem admission032_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (657424236755973687/8262301096345600000:ℝ) admission032_04_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission032_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_04_coefficients]
def admission032_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4552643562358852234557840687104/1477414565625:ℝ),(8194875715047407809031902855168/886448739375:ℝ),(40974964506333918831452033646592/4432243696875:ℝ),(13658516618173436489966041432064/4432243696875:ℝ)],
![(606638853574530618148041785344/98494304375:ℝ),(409487108640828822932529656889344/22161218484375:ℝ),(409492985289162258975679961890816/22161218484375:ℝ),(136499618702602825126459706703872/22161218484375:ℝ)],
![(4546939241259107037662786093056/1477414565625:ℝ),(6600490831117536377636518887424/714878015625:ℝ),(204618162757492664818419793657856/22161218484375:ℝ),(68207035611735642676629499543552/22161218484375:ℝ)]]
theorem admission032_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (3252224379486398962256517/69309205075213470924800000:ℝ) admission032_05_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission032_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_05_coefficients]
def admission032_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(103492154744464009768592846606330494976/13783362654322956795:ℝ),(13965984478660092280675186865761276657664/620251319444533055775:ℝ),(450339642599313059887273448256290422784/20008107078855905025:ℝ),(310112760358836390659216953137906581504/41350087962968870385:ℝ)],
![(129389045050556853765129359431601546592256/8614601658951847996875:ℝ),(17460700137765797440668276364209947416723456/387657074652833159859375:ℝ),(17453880260979019880172943891698017753890816/387657074652833159859375:ℝ),(387712476696139486716262399007342662254592/25843804976855543990625:ℝ)],
![(64706448335266847659758830302644987232256/8614601658951847996875:ℝ),(8731959838603239765246284573109149505683456/387657074652833159859375:ℝ),(8728549685617329344857020831732390812450816/387657074652833159859375:ℝ),(193892001471866742554251803296151048814592/25843804976855543990625:ℝ)]]
theorem admission032_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (8813934765579358289051497/77082150819303193302794240:ℝ) admission032_06_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission032_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_06_coefficients]
def admission032_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33425197296984140058863628297426408833024/2095443646772071134375:ℝ),(100258500162023109319143508802346860675072/2095443646772071134375:ℝ),(100241409497852014230030480131272392835072/2095443646772071134375:ℝ),(33408106632813044969750599626351940993024/2095443646772071134375:ℝ)],
![(66834086715947737297348516419940705632256/2095443646772071134375:ℝ),(1002340404307626051061715616096032267436032/10477218233860355671875:ℝ),(1002169518522318834388321196132140425674752/10477218233860355671875:ℝ),(106879855294218070340271411883459739648/3352709834835313815:ℝ)],
![(33408889418963597238484888122514296799232/2095443646772071134375:ℝ),(501047903497510504465998072084297964060672/10477218233860355671875:ℝ),(500962471033058763238168795475778461499392/10477218233860355671875:ℝ),(33391802926073248992919032800810396286976/2095443646772071134375:ℝ)]]
theorem admission032_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (474526060061084095208898259/1953095037651263343820800000:ℝ) admission032_07_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission032_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_07_coefficients]
def admission032_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(212005777638341779884556663048783099649553664/1364221124200567144775390625:ℝ),(382071780612339479730833932572161244187920128/818532674520340286865234375:ℝ),(1912665737775045837038674621481001962128335616/4092663372601701434326171875:ℝ),(212774722527899228282162642486495141445798656/1364221124200567144775390625:ℝ)],
![(2130756105319992757681343281849022296169245696/6821105621002835723876953125:ℝ),(3839971046320019309457360601740532241488905728/4092663372601701434326171875:ℝ),(19222904821665822214955414614666833546206305792/20463316863008507171630859375:ℝ),(427687860371926558488936086091826616897967616/1364221124200567144775390625:ℝ)],
![(1070727217128283858258559966605106797921477376/6821105621002835723876953125:ℝ),(1929612143258321910803190938879726020549305088/4092663372601701434326171875:ℝ),(9659576132790593029762041507261823735564627712/20463316863008507171630859375:ℝ),(42982627568805466041354688721066295090433792/272844224840113428955078125:ℝ)]]
theorem admission032_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (828147568899772577674049465034308983006069/349519971362169363116414153523200000000000000:ℝ) admission032_08_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission032_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_08_coefficients]
def admission032_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3694549373441742042634490945034413753400832/6548261396162722294921875:ℝ),(11076556570053221692683402277567582657052672/6548261396162722294921875:ℝ),(3689821836384242622458070873445828501962752/2182753798720907431640625:ℝ),(3687458312600782064119801209270167631036416/6548261396162722294921875:ℝ)],
![(36889113524207031901138296452201608472607232/32741306980813611474609375:ℝ),(22119291194203208868481123741904177608523776/6548261396162722294921875:ℝ),(36841858753126838927113362064177222821871616/10913768993604537158203125:ℝ),(1472729352526676091295607409108580856496128/1309652279232544458984375:ℝ)],
![(18416366656998321687965841727029539705603072/32741306980813611474609375:ℝ),(11042734624149987175797721464336594951471104/6548261396162722294921875:ℝ),(18392749571205625814823007696948080312057856/10913768993604537158203125:ℝ),(3676188450032598392358235836272736651444224/6548261396162722294921875:ℝ)]]
theorem admission032_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (417934239752935172004781160953/48827375941281583595520000000000:ℝ) admission032_09_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission032_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_09_coefficients]
def admission032_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1146078144394181926378276336666496/7694867529296875:ℝ),(30919697518043736105869510261310592/69253807763671875:ℝ),(30895286370729940904066473182625792/69253807763671875:ℝ),(1143365794709283908404501383479296/7694867529296875:ℝ)],
![(20594115564203731001777133238348288/69253807763671875:ℝ),(20577845901301935696336873838596608/23084602587890625:ℝ),(20561577059968857427804648062844928/23084602587890625:ℝ),(20545309040503982101649205911093248/69253807763671875:ℝ)],
![(10279404392354890305557033945923072/69253807763671875:ℝ),(6162763314616870662346256872454656/13850761552734375:ℝ),(30789421200524384330564297733177344/69253807763671875:ℝ),(10255009019944694195796297316827136/69253807763671875:ℝ)]]
theorem admission032_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4775360701579923832694207/2115149080664473600000000000:ℝ) admission032_10_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission032_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_10_coefficients]
def admission032_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137096022277227632797689216512652941983744/10477218233860355671875:ℝ),(137072724441138128200600129129288705245184/3492406077953451890625:ℝ),(137049428305394865412087530474707158564864/3492406077953451890625:ℝ),(137026133869997844432151420548908301942784/10477218233860355671875:ℝ)],
![(54824699454382170495749348075714702737408/2095443646772071134375:ℝ),(274076907556037503024135572196421739216896/3492406077953451890625:ℝ),(274030321240408679879029303493972046381056/3492406077953451890625:ℝ),(54796747665004876608685586854244887035904/2095443646772071134375:ℝ)],
![(137027474994683219681057523865920571703296/10477218233860355671875:ℝ),(137004183114899374823535443067133033971712/3492406077953451890625:ℝ),(136980892935013814466941773019264887816192/3492406077953451890625:ℝ),(136957604455026538611276513722316133236736/10477218233860355671875:ℝ)]]
theorem admission032_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1946284619052484836903382099/9765475188256316719104000000:ℝ) admission032_11_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission032_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_11_coefficients]
def admission032_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(237116164447122183763787776/439453125:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/439453125:ℝ)],
![(474232328894244367527575552/439453125:ℝ),(474232328894244367527575552/146484375:ℝ),(474232328894244367527575552/146484375:ℝ),(474232328894244367527575552/439453125:ℝ)],
![(237116164447122183763787776/439453125:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/439453125:ℝ)]]
theorem admission032_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission032_12_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission032_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_12_coefficients]
def admission032_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(75094841405859701161315008512/274658203125:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/274658203125:ℝ)],
![(150189682811719402322630017024/274658203125:ℝ),(150189682811719402322630017024/91552734375:ℝ),(150189682811719402322630017024/91552734375:ℝ),(150189682811719402322630017024/274658203125:ℝ)],
![(75094841405859701161315008512/274658203125:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/274658203125:ℝ)]]
theorem admission032_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission032_13_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission032_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_13_coefficients]
def admission032_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)],
![(590295810358705651712/9:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/9:ℝ)],
![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)]]
theorem admission032_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission032_14_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission032_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_14_coefficients]
theorem admission032_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission032_00_pos hd hp
 · exact admission032_01_pos hd hp
 · exact admission032_02_pos hd hp
 · exact admission032_03_pos hd hp
 · exact admission032_04_pos hd hp
 · exact admission032_05_pos hd hp
 · exact admission032_06_pos hd hp
 · exact admission032_07_pos hd hp
 · exact admission032_08_pos hd hp
 · exact admission032_09_pos hd hp
 · exact admission032_10_pos hd hp
 · exact admission032_11_pos hd hp
 · exact admission032_12_pos hd hp
 · exact admission032_13_pos hd hp
 · exact admission032_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission032_all
