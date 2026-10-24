/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission005_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(873745047558815744/472772661:ℝ),(7767715355216052224/1418317983:ℝ),(7671725282402762752/1418317983:ℝ),(2525245069863157760/1418317983:ℝ)],
![(1747490095117631488/472772661:ℝ),(15535430710432104448/1418317983:ℝ),(15343450564805525504/1418317983:ℝ),(5050490139726315520/1418317983:ℝ)],
![(873745047558815744/472772661:ℝ),(7767715355216052224/1418317983:ℝ),(7671725282402762752/1418317983:ℝ),(2525245069863157760/1418317983:ℝ)]]
theorem admission005_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission005_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission005_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_00_coefficients]
def admission005_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1902084455250526208/1418317983:ℝ),(5652566274551578624/1418317983:ℝ),(5598879183351578624/1418317983:ℝ),(205377484894502912/157590887:ℝ)],
![(3804168910501052416/1418317983:ℝ),(11305132549103157248/1418317983:ℝ),(11197758366703157248/1418317983:ℝ),(410754969789005824/157590887:ℝ)],
![(1902084455250526208/1418317983:ℝ),(5652566274551578624/1418317983:ℝ),(5598879183351578624/1418317983:ℝ),(205377484894502912/157590887:ℝ)]]
theorem admission005_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission005_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission005_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_01_coefficients]
def admission005_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3019076058582087630848/4432243696875:ℝ),(14960800059271898202112/7387072828125:ℝ),(14826219825633358249984/7387072828125:ℝ),(14691639591994818297856/22161218484375:ℝ)],
![(6038152117164175261696/4432243696875:ℝ),(29921600118543796404224/7387072828125:ℝ),(29652439651266716499968/7387072828125:ℝ),(29383279183989636595712/22161218484375:ℝ)],
![(3019076058582087630848/4432243696875:ℝ),(14960800059271898202112/7387072828125:ℝ),(14826219825633358249984/7387072828125:ℝ),(14691639591994818297856/22161218484375:ℝ)]]
theorem admission005_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission005_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission005_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_02_coefficients]
def admission005_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1485462980570120192/1418317983:ℝ),(13142158770798854144/4254953949:ℝ),(12916271382066626560/4254953949:ℝ),(4230501552978132992/4254953949:ℝ)],
![(2933277859291070464/1418317983:ℝ),(25945825865157836800/4254953949:ℝ),(25494421819096039424/4254953949:ℝ),(8348429531811414016/4254953949:ℝ)],
![(1447814878720950272/1418317983:ℝ),(12803667094358982656/4254953949:ℝ),(12578150437029412864/4254953949:ℝ),(4117927978833281024/4254953949:ℝ)]]
theorem admission005_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (245447634389/484119204864:ℝ) admission005_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission005_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_03_coefficients]
def admission005_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1189446361804534456832/7387072828125:ℝ),(693670287852073859584/1477414565625:ℝ),(3369300203424200261632/7387072828125:ℝ),(1090395125968365420544/7387072828125:ℝ)],
![(2438888552234671542016/7387072828125:ℝ),(7114059110551408742144/7387072828125:ℝ),(6913350027409697800192/7387072828125:ℝ),(746059823030986866688/2462357609375:ℝ)],
![(1249442190430137085184/7387072828125:ℝ),(1215235890430346481408/2462357609375:ℝ),(236269988265699835904/492471521875:ℝ),(229556868624919035904/1477414565625:ℝ)]]
theorem admission005_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478581916447053/161373068288000000:ℝ) admission005_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission005_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_04_coefficients]
def admission005_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74959297776489878144/714878015625:ℝ),(1395142492191294184064/4432243696875:ℝ),(6978859614068188064384/22161218484375:ℝ),(775628461394301122176/7387072828125:ℝ)],
![(139370480760528512512/714878015625:ℝ),(12978788153204661168128/22161218484375:ℝ),(12993384823927485846784/22161218484375:ℝ),(1445027191433069522176/7387072828125:ℝ)],
![(64411182984038634368/714878015625:ℝ),(6003075692248190247808/22161218484375:ℝ),(240581008394371911296/886448739375:ℝ),(71402531204135296/787954435:ℝ)]]
theorem admission005_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (503212367062801831/10661033672704000000:ℝ) admission005_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission005_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_05_coefficients]
def admission005_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(95138208121468049125811824809472/387657074652833159859375:ℝ),(90812146920659819291680883732992/129219024884277719953125:ℝ),(259711991275491756970555680948224/387657074652833159859375:ℝ),(5494159261256452228088323637248/25843804976855543990625:ℝ)],
![(194482251987784452162961645745408/387657074652833159859375:ℝ),(185758993255973915440956348524288/129219024884277719953125:ℝ),(531619121638969005701236515045376/387657074652833159859375:ℝ),(11254774558760211489421941014528/25843804976855543990625:ℝ)],
![(99344043866316403037149820935936/387657074652833159859375:ℝ),(94946846335314096149275464791296/129219024884277719953125:ℝ),(271907130363477248730680834097152/387657074652833159859375:ℝ),(1152123059500751852266723475456/5168760995371108798125:ℝ)]]
theorem admission005_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (20958554310823258316376967/188188844773689436774400000:ℝ) admission005_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission005_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_06_coefficients]
def admission005_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1837111194066214217179296921088/3492406077953451890625:ℝ),(16199475790212622241235354214912/10477218233860355671875:ℝ),(15867576776860127601376723140608/10477218233860355671875:ℝ),(1035886913769229602335851937792/2095443646772071134375:ℝ)],
![(3569654388652786082433793156352/3492406077953451890625:ℝ),(31467942687818026239377048776448/10477218233860355671875:ℝ),(30814168456818313643413906358272/10477218233860355671875:ℝ),(2011037786991729130267647410176/2095443646772071134375:ℝ)],
![(1732543194586571865254496235264/3492406077953451890625:ℝ),(15268466897605403998141694561536/10477218233860355671875:ℝ),(14946591679958186042037183217664/10477218233860355671875:ℝ),(975150873222499527931795472384/2095443646772071134375:ℝ)]]
theorem admission005_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (7439810739307399962858547/30517109963300989747200000:ℝ) admission005_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission005_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_07_coefficients]
def admission005_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14169344403832419604571688311/851750962039896240234375:ℝ),(195167996216561148213919069679087/73345221731213287353515625:ℝ),(107596076337372430846730906717093603/20463316863008507171630859375:ℝ),(10694274785410572674579362654535021/4092663372601701434326171875:ℝ)],
![(26901672710993994783021244592039/4258754810199481201171875:ℝ),(579945712559607858966456077931551/24448407243737762451171875:ℝ),(582614887972684064027548363917792262/20463316863008507171630859375:ℝ),(45287203064584300741836819802328794/4092663372601701434326171875:ℝ)],
![(26830825988974832684998386150484/4258754810199481201171875:ℝ),(1544669141462262428685449164115566/73345221731213287353515625:ℝ),(475018811635311633180817457200698659/20463316863008507171630859375:ℝ),(34592928279173728067257457147793773/4092663372601701434326171875:ℝ)]]
theorem admission005_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (14169344403832419604571688311/1625885567243507466240000000000000:ℝ) admission005_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission005_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_08_coefficients]
def admission005_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(181210826676890390131127404769864/6548261396162722294921875:ℝ),(2567077823890683517059212547363392/32741306980813611474609375:ℝ),(805786425105957682953269598408704/10913768993604537158203125:ℝ),(151270648253190857363211724177408/6548261396162722294921875:ℝ)],
![(317446084897060185945505216293724/6548261396162722294921875:ℝ),(4474711945360755599815560564437728/32741306980813611474609375:ℝ),(1396744892467978189342345148594176/10913768993604537158203125:ℝ),(260557786816128010828360991965184/6548261396162722294921875:ℝ)],
![(27247051644033959162875562304772/1309652279232544458984375:ℝ),(1907634121470072082756348017074336/32741306980813611474609375:ℝ),(590958467362020506389075550185472/10913768993604537158203125:ℝ),(109287138562937153465149267787776/6548261396162722294921875:ℝ)]]
theorem admission005_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (6670357578304269620675614489/762927749082524743680000000000:ℝ) admission005_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission005_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_09_coefficients]
def admission005_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(532136306994874083198052/69253807763671875:ℝ),(19948056312596558862956/923384103515625:ℝ),(1396483280786621551111744/69253807763671875:ℝ),(432523994493003719588096/69253807763671875:ℝ)],
![(934056347719300232356564/69253807763671875:ℝ),(28050951922834649179172/744664599609375:ℝ),(96662705005762417970752/2770152310546875:ℝ),(741903158570988307962368/69253807763671875:ℝ)],
![(44212569794958303869273/7694867529296875:ℝ),(122319105407863332202793/7694867529296875:ℝ),(336192351895309826040176/23084602587890625:ℝ),(101875775173782241039616/23084602587890625:ℝ)]]
theorem admission005_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1193856740317760637183/516393818521600000000000:ℝ) admission005_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission005_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_10_coefficients]
def admission005_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4527486986771278970459297750528/10477218233860355671875:ℝ),(4435898466229628307404369136128/3492406077953451890625:ℝ),(4345150851937113117354548166656/3492406077953451890625:ℝ),(4255244143893733400309834842112/10477218233860355671875:ℝ)],
![(1758216140676296813090583682304/2095443646772071134375:ℝ),(1722159621049102850627111558912/698481215590690378125:ℝ),(8432169978463549757069021396992/3492406077953451890625:ℝ),(8255196323035590577253309218816/10477218233860355671875:ℝ)],
![(4263593716610205094993620660992/10477218233860355671875:ℝ),(4174899639015885945731188658432/3492406077953451890625:ℝ),(4087019126526436639714473230336/3492406077953451890625:ℝ),(3999952179141857176943474376704/10477218233860355671875:ℝ)]]
theorem admission005_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (30517213280806405463741107/152585549816504948736000000:ℝ) admission005_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission005_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_11_coefficients]
def admission005_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)],
![(13801977297240064/439453125:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/439453125:ℝ)],
![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)]]
theorem admission005_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission005_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission005_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_12_coefficients]
def admission005_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2185547532451446784/274658203125:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/274658203125:ℝ)],
![(4371095064902893568/274658203125:ℝ),(4371095064902893568/91552734375:ℝ),(4371095064902893568/91552734375:ℝ),(4371095064902893568/274658203125:ℝ)],
![(2185547532451446784/274658203125:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/274658203125:ℝ)]]
theorem admission005_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission005_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission005_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_13_coefficients]
def admission005_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission005_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission005_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission005_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_14_coefficients]
theorem admission005_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission005_00_pos hd hp
 · exact admission005_01_pos hd hp
 · exact admission005_02_pos hd hp
 · exact admission005_03_pos hd hp
 · exact admission005_04_pos hd hp
 · exact admission005_05_pos hd hp
 · exact admission005_06_pos hd hp
 · exact admission005_07_pos hd hp
 · exact admission005_08_pos hd hp
 · exact admission005_09_pos hd hp
 · exact admission005_10_pos hd hp
 · exact admission005_11_pos hd hp
 · exact admission005_12_pos hd hp
 · exact admission005_13_pos hd hp
 · exact admission005_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission005_all
