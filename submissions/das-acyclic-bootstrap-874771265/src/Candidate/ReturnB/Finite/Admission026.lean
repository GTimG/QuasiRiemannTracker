/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission026_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(294911353309858027798528/157590887:ℝ),(7956315733954275011723264/1418317983:ℝ),(7950024928542383272886272/1418317983:ℝ),(2647911374376830511349760/1418317983:ℝ)],
![(589822706619716055597056/157590887:ℝ),(15912631467908550023446528/1418317983:ℝ),(15900049857084766545772544/1418317983:ℝ),(5295822748753661022699520/1418317983:ℝ)],
![(294911353309858027798528/157590887:ℝ),(7956315733954275011723264/1418317983:ℝ),(7950024928542383272886272/1418317983:ℝ),(2647911374376830511349760/1418317983:ℝ)]]
theorem admission026_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission026_00_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission026_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_00_coefficients]
def admission026_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1941703551615527769079808/1418317983:ℝ),(5821592217637700107239424/1418317983:ℝ),(5818073780428816907239424/1418317983:ℝ),(215353901600738285453312/157590887:ℝ)],
![(3883407103231055538159616/1418317983:ℝ),(11643184435275400214478848/1418317983:ℝ),(11636147560857633814478848/1418317983:ℝ),(430707803201476570906624/157590887:ℝ)],
![(1941703551615527769079808/1418317983:ℝ),(5821592217637700107239424/1418317983:ℝ),(5818073780428816907239424/1418317983:ℝ),(215353901600738285453312/157590887:ℝ)]]
theorem admission026_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission026_01_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission026_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_01_coefficients]
def admission026_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3086352045478152930880126976/4432243696875:ℝ),(15422940377199029300097974272/7387072828125:ℝ),(15414120527007293945795313664/7387072828125:ℝ),(15405300676815558591492653056/22161218484375:ℝ)],
![(6172704090956305861760253952/4432243696875:ℝ),(30845880754398058600195948544/7387072828125:ℝ),(30828241054014587891590627328/7387072828125:ℝ),(30810601353631117182985306112/22161218484375:ℝ)],
![(3086352045478152930880126976/4432243696875:ℝ),(15422940377199029300097974272/7387072828125:ℝ),(15414120527007293945795313664/7387072828125:ℝ),(15405300676815558591492653056/22161218484375:ℝ)]]
theorem admission026_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission026_02_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission026_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_02_coefficients]
def admission026_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(160605853823393469562880/157590887:ℝ),(12994360654631659548704768/4254953949:ℝ),(12979651860610700862816256/4254953949:ℝ),(4321649259210664992309248/4254953949:ℝ)],
![(962815205882895227944960/472772661:ℝ),(25966585172924034269052928/4254953949:ℝ),(25937169216644150183591936/4254953949:ℝ),(8635920896666172966043648/4254953949:ℝ)],
![(480997644412714819256320/472772661:ℝ),(12972224518292374720348160/4254953949:ℝ),(12957517356033449320775680/4254953949:ℝ),(4314271637455507973734400/4254953949:ℝ)]]
theorem admission026_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (3923807196275/7745907277824:ℝ) admission026_03_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission026_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_03_coefficients]
def admission026_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(393351279698439070670651392/2462357609375:ℝ),(235570291947374041587777536/492471521875:ℝ),(1175650392535701179630354432/2462357609375:ℝ),(391150212497270042362118144/2462357609375:ℝ)],
![(25418057204086417975083008/79430890625:ℝ),(7078413095427128364628639744/7387072828125:ℝ),(11304313776266019872964608/11819316525:ℝ),(3761059735550673484251136/11819316525:ℝ)],
![(394608493628239886556921856/2462357609375:ℝ),(3544858716216517740811976704/7387072828125:ℝ),(3538244932559158881711816704/7387072828125:ℝ),(1177211697227360800570605568/7387072828125:ℝ)]]
theorem admission026_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25613931302180793/322746136576000000:ℝ) admission026_04_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission026_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_04_coefficients]
def admission026_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2109870631023881561304498176/22161218484375:ℝ),(6330282760863831520969326592/22161218484375:ℝ),(6330947950956448736144359424/22161218484375:ℝ),(703511940372166258826510336/7387072828125:ℝ)],
![(4198821777023587773423026176/22161218484375:ℝ),(12597840945755841281544814592/22161218484375:ℝ),(12599205195942902483639271424/22161218484375:ℝ),(466687336356738775057498112/2462357609375:ℝ)],
![(16711609167997649696948224/177289747875:ℝ),(50140465479136078084603904/177289747875:ℝ),(50146057959891629979959296/177289747875:ℝ),(5572400549584400530767872/59096582625:ℝ)]]
theorem admission026_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (509997838378834524443/10829563293002104832000:ℝ) admission026_05_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission026_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_05_coefficients]
def admission026_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2882037070148941396545046209564246016/12505066924284940640625:ℝ),(9896163186665446780757824158479417344/14357669431586413328125:ℝ),(266364405883173877721501978941825482752/387657074652833159859375:ℝ),(5900743243863273761366050610624856064/25843804976855543990625:ℝ)],
![(178949074516261901706058052980045316096/387657074652833159859375:ℝ),(59464477804803703228048744416276447232/43073008294759239984375:ℝ),(533515460705068698502770018643389448192/387657074652833159859375:ℝ),(2363789790103610207292572958359289856/5168760995371108798125:ℝ)],
![(3584237013665788736526464819342147584/15506282986113326394375:ℝ),(1191039529792294515431010877633527808/1722920331790369599375:ℝ),(53430210964378964156253607940312793088/77531414930566631971875:ℝ),(5918205706654777275096814181171593216/25843804976855543990625:ℝ)]]
theorem admission026_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (42933557734528394658744587/376377689547378873548800000:ℝ) admission026_06_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission026_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_06_coefficients]
def admission026_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(190499553778896776689719939464953856/388045119772605765625:ℝ),(15409515476123215875922139898824359936/10477218233860355671875:ℝ),(15388577527176957485693113990815678464/10477218233860355671875:ℝ),(1024510000616790916078682491509014528/2095443646772071134375:ℝ)],
![(1140781462818417897370102696997224448/1164135359317817296875:ℝ),(30759243509393342608513215368056733696/10477218233860355671875:ℝ),(30717408364429138182188394787586965504/10477218233860355671875:ℝ),(2045039604080311330001220738501050368/2095443646772071134375:ℝ)],
![(113856560296345513460188575720472576/232827071863563459375:ℝ),(3069945606654025346518215093846474752/2095443646772071134375:ℝ),(3065766167450436139299056159354257408/2095443646772071134375:ℝ),(204105920692704082784507649398407168/419088729354414226875:ℝ)]]
theorem admission026_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (23761056444223979812174529/97654751882563167191040000:ℝ) admission026_07_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission026_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_07_coefficients]
def admission026_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17884738917837815438139618883201572540928/4092663372601701434326171875:ℝ),(90382651840868934362588124734638217819648/6821105621002835723876953125:ℝ),(274024096310121190474125178108039887778304/20463316863008507171630859375:ℝ),(738398655163595597123263722420005576192/163706534904068057373046875:ℝ)],
![(37343033474531696635103417252126059149248/4092663372601701434326171875:ℝ),(188620847013570391492328268441061328850688/6821105621002835723876953125:ℝ),(571578155203874863930902906611847887709184/20463316863008507171630859375:ℝ),(38486154913547042007977737721710484380672/4092663372601701434326171875:ℝ)],
![(3891658911338776239392759673784897321664/818532674520340286865234375:ℝ),(19647639034540291425948028741284622206208/1364221124200567144775390625:ℝ),(1919703605766152731979211151637470967296/132021399116183917236328125:ℝ),(20026188534457152079896144661210344975872/4092663372601701434326171875:ℝ)]]
theorem admission026_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (34931130698901983277616443131253071369/15999754548439149312579993600000000000000:ℝ) admission026_08_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission026_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_08_coefficients]
def admission026_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(117723267227332741491312484950887035904/6548261396162722294921875:ℝ),(1757085736946873364768437948761156222976/32741306980813611474609375:ℝ),(582775775809237239465274689142308995072/10913768993604537158203125:ℝ),(115971586251300622001204069190810468352/6548261396162722294921875:ℝ)],
![(232683023635853381792395332621625951936/6548261396162722294921875:ℝ),(3472779267787127540293729371010853134336/32741306980813611474609375:ℝ),(1151774282126709374417857652860200681472/10913768993604537158203125:ℝ),(229191741211540777263744717239670013952/6548261396162722294921875:ℝ)],
![(3708379238984536783905898311959319872/211234238585894267578125:ℝ),(343138706168050835105058284449939382272/6548261396162722294921875:ℝ),(22759940252698885398103318548715667456/436550759744181486328125:ℝ),(4528806198409606210501625921954381824/261930455846508891796875:ℝ)]]
theorem admission026_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4217779448637372078841203751/488273759412815835955200000000:ℝ) admission026_09_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission026_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_09_coefficients]
def admission026_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(66154807152341521556901515264/13850761552734375:ℝ),(328769290628671796453292224512/23084602587890625:ℝ),(108921787371455622610386157568/7694867529296875:ℝ),(324762252545922821918106320896/69253807763671875:ℝ)],
![(130591054614857821414843315712/13850761552734375:ℝ),(129791199683980767070293979648/4616920517578125:ℝ),(386975008405234992151683530752/13850761552734375:ℝ),(8546164326699617490376327168/923384103515625:ℝ)],
![(34364352562692113644428016/7387072828125:ℝ),(102454815127574909169136112/7387072828125:ℝ),(9853241689156149498277888/714878015625:ℝ),(20235821083252512074498048/4432243696875:ℝ)]]
theorem admission026_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (19298382838490020823/8460596322657894400000:ℝ) admission026_10_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission026_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_10_coefficients]
def admission026_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4219747318776237550908233395639156736/10477218233860355671875:ℝ),(4214034634587102657480204304589520896/3492406077953451890625:ℝ),(168333011310425492437204386745155584/139696243118138075625:ℝ),(4202619263296841511257949487757262848/10477218233860355671875:ℝ)],
![(8422728907373522008113758376056651776/10477218233860355671875:ℝ),(8411315184653576531101642136658313216/3492406077953451890625:ℝ),(1679981623931927443168835280664788992/698481215590690378125:ℝ),(8388507712391704062341361176053547008/10477218233860355671875:ℝ)],
![(840596317719456891441104996083499008/2095443646772071134375:ℝ),(839456110013294774724287566413758464/698481215590690378125:ℝ),(838316567379799980982813346939011072/698481215590690378125:ℝ),(837177689818972510216682337659256832/2095443646772071134375:ℝ)]]
theorem admission026_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (97460310186605494261798721/488273759412815835955200000:ℝ) admission026_11_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission026_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_11_coefficients]
def admission026_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7236211073215398674432/439453125:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/439453125:ℝ)],
![(14472422146430797348864/439453125:ℝ),(14472422146430797348864/146484375:ℝ),(14472422146430797348864/146484375:ℝ),(14472422146430797348864/439453125:ℝ)],
![(7236211073215398674432/439453125:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/439453125:ℝ)]]
theorem admission026_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission026_12_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission026_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_12_coefficients]
def admission026_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2291712689387808262979584/274658203125:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/274658203125:ℝ)],
![(4583425378775616525959168/274658203125:ℝ),(4583425378775616525959168/91552734375:ℝ),(4583425378775616525959168/91552734375:ℝ),(4583425378775616525959168/274658203125:ℝ)],
![(2291712689387808262979584/274658203125:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/274658203125:ℝ)]]
theorem admission026_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission026_13_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission026_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_13_coefficients]
def admission026_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)],
![(18014398509481984/9:ℝ),(18014398509481984/3:ℝ),(18014398509481984/3:ℝ),(18014398509481984/9:ℝ)],
![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)]]
theorem admission026_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission026_14_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission026_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_14_coefficients]
theorem admission026_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission026_00_pos hd hp
 · exact admission026_01_pos hd hp
 · exact admission026_02_pos hd hp
 · exact admission026_03_pos hd hp
 · exact admission026_04_pos hd hp
 · exact admission026_05_pos hd hp
 · exact admission026_06_pos hd hp
 · exact admission026_07_pos hd hp
 · exact admission026_08_pos hd hp
 · exact admission026_09_pos hd hp
 · exact admission026_10_pos hd hp
 · exact admission026_11_pos hd hp
 · exact admission026_12_pos hd hp
 · exact admission026_13_pos hd hp
 · exact admission026_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission026_all
