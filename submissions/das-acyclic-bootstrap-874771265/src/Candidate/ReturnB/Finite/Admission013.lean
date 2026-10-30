/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission013_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(873745047558815744/472772661:ℝ),(7767715355216052224/1418317983:ℝ),(7671725282402762752/1418317983:ℝ),(2525245069863157760/1418317983:ℝ)],
![(1747490095117631488/472772661:ℝ),(15535430710432104448/1418317983:ℝ),(15343450564805525504/1418317983:ℝ),(5050490139726315520/1418317983:ℝ)],
![(873745047558815744/472772661:ℝ),(7767715355216052224/1418317983:ℝ),(7671725282402762752/1418317983:ℝ),(2525245069863157760/1418317983:ℝ)]]
theorem admission013_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission013_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission013_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_00_coefficients]
def admission013_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1902084455250526208/1418317983:ℝ),(5652566274551578624/1418317983:ℝ),(5598879183351578624/1418317983:ℝ),(205377484894502912/157590887:ℝ)],
![(3804168910501052416/1418317983:ℝ),(11305132549103157248/1418317983:ℝ),(11197758366703157248/1418317983:ℝ),(410754969789005824/157590887:ℝ)],
![(1902084455250526208/1418317983:ℝ),(5652566274551578624/1418317983:ℝ),(5598879183351578624/1418317983:ℝ),(205377484894502912/157590887:ℝ)]]
theorem admission013_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission013_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission013_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_01_coefficients]
def admission013_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3019076058582087630848/4432243696875:ℝ),(14960800059271898202112/7387072828125:ℝ),(14826219825633358249984/7387072828125:ℝ),(14691639591994818297856/22161218484375:ℝ)],
![(6038152117164175261696/4432243696875:ℝ),(29921600118543796404224/7387072828125:ℝ),(29652439651266716499968/7387072828125:ℝ),(29383279183989636595712/22161218484375:ℝ)],
![(3019076058582087630848/4432243696875:ℝ),(14960800059271898202112/7387072828125:ℝ),(14826219825633358249984/7387072828125:ℝ),(14691639591994818297856/22161218484375:ℝ)]]
theorem admission013_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission013_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission013_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_02_coefficients]
def admission013_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1466577141078425600/1418317983:ℝ),(12972527455576260608/4254953949:ℝ),(12747010798246690816/4254953949:ℝ),(4174214765905707008/4254953949:ℝ)],
![(2895506180307681280/1418317983:ℝ),(25606563234712649728/4254953949:ℝ),(25155900651456167936/4254953949:ℝ),(8235855957666562048/4254953949:ℝ)],
![(1428929039229255680/1418317983:ℝ),(12634035779136389120/4254953949:ℝ),(12408889853209477120/4254953949:ℝ),(4061641191760855040/4254953949:ℝ)]]
theorem admission013_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (30261585055/60514900608:ℝ) admission013_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission013_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_03_coefficients]
def admission013_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(406915860617340735232/2462357609375:ℝ),(237308256370446320384/492471521875:ℝ),(1152655332750384300032/2462357609375:ℝ),(373029911515493433344/2462357609375:ℝ)],
![(833830330776549013248/2462357609375:ℝ),(7296603923144059757824/7387072828125:ℝ),(1418136323412720615424/1477414565625:ℝ),(459113737249838071808/1477414565625:ℝ)],
![(426914470159208278016/2462357609375:ℝ),(3736980077587364952064/7387072828125:ℝ),(3632715618812450177024/7387072828125:ℝ),(1176478951702710059008/7387072828125:ℝ)]]
theorem admission013_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25613931302180793/322746136576000000:ℝ) admission013_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission013_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_04_coefficients]
def admission013_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69685240380264256256/714878015625:ℝ),(6493563030097173083392/22161218484375:ℝ),(6505012547708280617984/22161218484375:ℝ),(241299107711033275392/2462357609375:ℝ)],
![(128822365968077268736/714878015625:ℝ),(387564170693098886912/714878015625:ℝ),(12045690691207670953984/22161218484375:ℝ),(1341564914910666930176/7387072828125:ℝ)],
![(11827425117562602496/142975603125:ℝ),(1104185252277778482176/4432243696875:ℝ),(44325425147995122688/177289747875:ℝ),(4941340734220536832/59096582625:ℝ)]]
theorem admission013_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (11550219841369729/266525841817600000:ℝ) admission013_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission013_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_05_coefficients]
def admission013_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(97345623594461600287810117885696/387657074652833159859375:ℝ),(92948426063459293399935761741056/129219024884277719953125:ℝ),(265911869547912840482661724946432/387657074652833159859375:ℝ),(5627387279380105744710970507264/25843804976855543990625:ℝ)],
![(198897082933771554486958231897856/387657074652833159859375:ℝ),(190031551541572863657466104540416/129219024884277719953125:ℝ),(471829035718830158478272856064/336216023116073859375:ℝ),(2304246119001503704533446950912/5168760995371108798125:ℝ)],
![(20310291867861990839829622802432/77531414930566631971875:ℝ),(19416625095622714051506068559872/25843804976855543990625:ℝ),(1794238765392892466082495987712/2501013384856988128125:ℝ),(5893843315627412777956264247296/25843804976855543990625:ℝ)]]
theorem admission013_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (42933557734528394658744587/376377689547378873548800000:ℝ) admission013_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission013_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_06_coefficients]
def admission013_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1783156561708846927257876623104/3492406077953451890625:ℝ),(15723987201705879556172118052096/10477218233860355671875:ℝ),(15402111984058661600067606708224/10477218233860355671875:ℝ),(1005518893495864565133823705088/2095443646772071134375:ℝ)],
![(3461745123938051502590952560384/3492406077953451890625:ℝ),(30516965510804540869250576450816/10477218233860355671875:ℝ),(29883238871215381640795673493504/10477218233860355671875:ℝ),(1950301746444999055863590944768/2095443646772071134375:ℝ)],
![(335717712445840915066615187456/698481215590690378125:ℝ),(2958595661819732262615691679744/2095443646772071134375:ℝ),(2896225377431344008145613357056/2095443646772071134375:ℝ),(188956570589826898145953447936/419088729354414226875:ℝ)]]
theorem admission013_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (180203028287722490449861/762927749082524743680000:ℝ) admission013_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission013_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_07_coefficients]
def admission013_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(26901672710993994783021244592039/8517509620398962402343750:ℝ),(1706739354131815210377162729936467/146690443462426574707031250:ℝ),(564292522137457274850382682477185783/40926633726017014343261718750:ℝ),(43469516482803056700431432167306777/8185326745203402868652343750:ℝ)],
![(53661651977949665369996772300968/4258754810199481201171875:ℝ),(3056240499377516490848692824372946/73345221731213287353515625:ℝ),(931715257435396477184469232960790839/20463316863008507171630859375:ℝ),(67368169976566212093109526660565529/4092663372601701434326171875:ℝ)],
![(80421631244905335956972300009897/8517509620398962402343750:ℝ),(58743221928309570284269638917459/1955872579499020996093750:ℝ),(259827598546667135903711156688879179/8185326745203402868652343750:ℝ),(91266823470329367485787621153824281/8185326745203402868652343750:ℝ)]]
theorem admission013_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (26901672710993994783021244592039/16258855672435074662400000000000000:ℝ) admission013_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission013_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_08_coefficients]
def admission013_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(157227013065296647763409039718676/6548261396162722294921875:ℝ),(2222510444146974861991816439996576/32741306980813611474609375:ℝ),(695917241587654766134231691159552/10913768993604537158203125:ℝ),(130278893408064005414180495982592/6548261396162722294921875:ℝ)],
![(269478457673872701210068486191348/6548261396162722294921875:ℝ),(3785577185873338289680768349704096/32741306980813611474609375:ℝ),(1177006525431372355704269334095872/10913768993604537158203125:ℝ),(218574277125874306930298535575552/6548261396162722294921875:ℝ)],
![(112251444608576053446659446472672/6548261396162722294921875:ℝ),(312613348345272685537790381941504/6548261396162722294921875:ℝ),(96217856768743517914007528587264/2182753798720907431640625:ℝ),(17659076743562060303223607918592/1309652279232544458984375:ℝ)]]
theorem admission013_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (134728063534256441522396911/19073193727063118592000000000:ℝ) admission013_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission013_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_09_coefficients]
def admission013_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(93022660239418219662701/13850761552734375:ℝ),(434157489266056360098427/23084602587890625:ℝ),(134464174979258729843408/7694867529296875:ℝ),(372827498563813086608896/69253807763671875:ℝ)],
![(158399302196826286783472/13850761552734375:ℝ),(48843340091427905923952/1538973505859375:ℝ),(80837665434178225766144/2770152310546875:ℝ),(41000432639955420766208/4616920517578125:ℝ)],
![(4305017296229852283584/923384103515625:ℝ),(11782873061439682895552/923384103515625:ℝ),(31970270894784706221056/2770152310546875:ℝ),(9537086099155214385152/2770152310546875:ℝ)]]
theorem admission013_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (582097540231641503/322746136576000000000:ℝ) admission013_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission013_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_10_coefficients]
def admission013_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4391239698986143206676800893696/10477218233860355671875:ℝ),(4302545621391824057414368891136/3492406077953451890625:ℝ),(842933021780474950279530692608/698481215590690378125:ℝ),(4127598161517795288626654609408/10477218233860355671875:ℝ)],
![(8518586127811212537887924697856/10477218233860355671875:ℝ),(8344092415569905753155557304576/3492406077953451890625:ℝ),(1634239698478814605031046397952/698481215590690378125:ℝ),(7999904358283714353886948753408/10477218233860355671875:ℝ)],
![(825469285765013866242224760832/2095443646772071134375:ℝ),(808309358835616339148237682688/698481215590690378125:ℝ),(791306676698339654751515705344/698481215590690378125:ℝ),(30978449574127352522082353152/83817745870882845375:ℝ)]]
theorem admission013_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (29543351720931389352877/152585549816504948736000:ℝ) admission013_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission013_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_11_coefficients]
def admission013_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)],
![(13801977297240064/439453125:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/439453125:ℝ)],
![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)]]
theorem admission013_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission013_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission013_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_12_coefficients]
def admission013_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2185547532451446784/274658203125:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/274658203125:ℝ)],
![(4371095064902893568/274658203125:ℝ),(4371095064902893568/91552734375:ℝ),(4371095064902893568/91552734375:ℝ),(4371095064902893568/274658203125:ℝ)],
![(2185547532451446784/274658203125:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/274658203125:ℝ)]]
theorem admission013_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission013_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission013_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_13_coefficients]
def admission013_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission013_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission013_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission013_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_14_coefficients]
theorem admission013_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission013_00_pos hd hp
 · exact admission013_01_pos hd hp
 · exact admission013_02_pos hd hp
 · exact admission013_03_pos hd hp
 · exact admission013_04_pos hd hp
 · exact admission013_05_pos hd hp
 · exact admission013_06_pos hd hp
 · exact admission013_07_pos hd hp
 · exact admission013_08_pos hd hp
 · exact admission013_09_pos hd hp
 · exact admission013_10_pos hd hp
 · exact admission013_11_pos hd hp
 · exact admission013_12_pos hd hp
 · exact admission013_13_pos hd hp
 · exact admission013_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission013_all
