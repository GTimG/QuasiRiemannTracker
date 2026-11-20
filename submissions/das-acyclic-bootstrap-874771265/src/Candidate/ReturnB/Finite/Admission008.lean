/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission008_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20785101446879796789248/1418317983:ℝ),(62257010506078581948416/1418317983:ℝ),(62158716671517773529088/1418317983:ℝ),(20686807612318988369920/1418317983:ℝ)],
![(41570202893759593578496/1418317983:ℝ),(124514021012157163896832/1418317983:ℝ),(124317433343035547058176/1418317983:ℝ),(41373615224637976739840/1418317983:ℝ)],
![(20785101446879796789248/1418317983:ℝ),(62257010506078581948416/1418317983:ℝ),(62158716671517773529088/1418317983:ℝ),(20686807612318988369920/1418317983:ℝ)]]
theorem admission008_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission008_00_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission008_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_00_coefficients]
def admission008_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15197046787690710695936/1418317983:ℝ),(45536164781683332087808/1418317983:ℝ),(45481189200294532087808/1418317983:ℝ),(1682452356255767855104/157590887:ℝ)],
![(30394093575381421391872/1418317983:ℝ),(91072329563366664175616/1418317983:ℝ),(90962378400589064175616/1418317983:ℝ),(3364904712511535710208/157590887:ℝ)],
![(15197046787690710695936/1418317983:ℝ),(45536164781683332087808/1418317983:ℝ),(45481189200294532087808/1418317983:ℝ),(1682452356255767855104/157590887:ℝ)]]
theorem admission008_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission008_01_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission008_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_01_coefficients]
def admission008_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(120767342015359146228973568/22161218484375:ℝ),(120629531856113281317994496/7387072828125:ℝ),(120491721696867416407015424/7387072828125:ℝ),(120353911537621551496036352/22161218484375:ℝ)],
![(241534684030718292457947136/22161218484375:ℝ),(241259063712226562635988992/7387072828125:ℝ),(240983443393734832814030848/7387072828125:ℝ),(240707823075243102992072704/22161218484375:ℝ)],
![(120767342015359146228973568/22161218484375:ℝ),(120629531856113281317994496/7387072828125:ℝ),(120491721696867416407015424/7387072828125:ℝ),(120353911537621551496036352/22161218484375:ℝ)]]
theorem admission008_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission008_02_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission008_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_02_coefficients]
def admission008_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34540747271908081270784/4254953949:ℝ),(103391793800843242766336/4254953949:ℝ),(103161489231159041720320/4254953949:ℝ),(34310442702223880224768/4254953949:ℝ)],
![(68850842350699625316352/4254953949:ℝ),(206091731591886354251776/4254953949:ℝ),(205631223965785832554496/4254953949:ℝ),(68390334724599103619072/4254953949:ℝ)],
![(34310095078791544045568/4254953949:ℝ),(102699937791043111485440/4254953949:ℝ),(102469734734626790834176/4254953949:ℝ),(34079892022375223394304/4254953949:ℝ)]]
theorem admission008_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (991855399403/1936476819456:ℝ) admission008_03_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission008_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_03_coefficients]
def admission008_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(97130175417042971459584/79430890625:ℝ),(26998609638982257891934208/7387072828125:ℝ),(26898020197130111071289344/7387072828125:ℝ),(8932516871932849525096448/7387072828125:ℝ)],
![(18184407516949715361685504/7387072828125:ℝ),(54351141384903863194836992/7387072828125:ℝ),(54149300728555805429727232/7387072828125:ℝ),(5994188953533885865525248/2462357609375:ℝ)],
![(9151301203164719015944192/7387072828125:ℝ),(9117510581973868434300928/2462357609375:ℝ),(9083760177141898119479296/2462357609375:ℝ),(9050049988668808071479296/7387072828125:ℝ)]]
theorem admission008_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478581916447053/161373068288000000:ℝ) admission008_04_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission008_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_04_coefficients]
def admission008_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1202399139585149570281472/1477414565625:ℝ),(54110146694081371174580224/22161218484375:ℝ),(54112159228158218712559616/22161218484375:ℝ),(18037999627854091092201472/22161218484375:ℝ)],
![(2361145418287471741042688/1477414565625:ℝ),(21251606645917843349192704/4432243696875:ℝ),(4250567029661477190787072/886448739375:ℝ),(1416932951450391565574144/886448739375:ℝ)],
![(386248759567440723587072/492471521875:ℝ),(1682189888242188566818816/714878015625:ℝ),(52152016513378711057117184/22161218484375:ℝ),(17385324158405698047152128/22161218484375:ℝ)]]
theorem admission008_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (848691122096427371163/16921192645315788800000:ℝ) admission008_05_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission008_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_05_coefficients]
def admission008_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45861898949460124863277614787526656/25843804976855543990625:ℝ),(2050947262680235675954889702989561856/387657074652833159859375:ℝ),(2038141090376984789830018689721696256/387657074652833159859375:ℝ),(45008152668212856652499547236335616/25843804976855543990625:ℝ)],
![(92273001270988588913278961040416768/25843804976855543990625:ℝ),(825311203346661129412486496133619712/77531414930566631971875:ℝ),(22166979195262036241683945437003776/2095443646772071134375:ℝ),(90562007298660198109085456052256768/25843804976855543990625:ℝ)],
![(46411102321528464050001346252890112/25843804976855543990625:ℝ),(2075608754053069971107542777678536704/387657074652833159859375:ℝ),(2062750060746491914881511216124002304/387657074652833159859375:ℝ),(45553854630447341456585908815921152/25843804976855543990625:ℝ)]]
theorem admission008_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (20958554310823258316376967/188188844773689436774400000:ℝ) admission008_06_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission008_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_06_coefficients]
def admission008_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8366906829981443671634357346172928/2095443646772071134375:ℝ),(125165754584296363467763241588948992/10477218233860355671875:ℝ),(4026717510954161796078117513592832/337974781737430828125:ℝ),(8299404481037974113766037612658688/2095443646772071134375:ℝ)],
![(16608916583536866008254295241121792/2095443646772071134375:ℝ),(49692120777391626956635992823422976/2095443646772071134375:ℝ),(49557625744891005983534265166462976/2095443646772071134375:ℝ),(16474421551036245035152567584161792/2095443646772071134375:ℝ)],
![(8242009753555422336619937894948864/2095443646772071134375:ℝ),(123294849302661771315416722528165888/10477218233860355671875:ℝ),(122959885884876014239249682910937088/10477218233860355671875:ℝ),(8175017069998270921386529971503104/2095443646772071134375:ℝ)]]
theorem admission008_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (30454311780625100886026509/122068439853203958988800000:ℝ) admission008_07_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission008_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_07_coefficients]
def admission008_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21483277141567368063829440518343133376/2273701873667611907958984375:ℝ),(634217022305412735002840747528447008448/20463316863008507171630859375:ℝ),(137668889862668594626776513486058049728/4092663372601701434326171875:ℝ),(27497412142510370378828486271320160064/2273701873667611907958984375:ℝ)],
![(70412804153554917910211987132113491088/2273701873667611907958984375:ℝ),(2007184106422365268519190872838123813536/20463316863008507171630859375:ℝ),(2113144924775311999020478471763178645376/20463316863008507171630859375:ℝ),(27395393716345236223701349647953055616/757900624555870635986328125:ℝ)],
![(48929527011987549846382546613770357712/2273701873667611907958984375:ℝ),(1372967084116952533516350125309676805088/20463316863008507171630859375:ℝ),(1424800475461969025886595904332888396736/20463316863008507171630859375:ℝ),(54688769006525338292275562672539006784/2273701873667611907958984375:ℝ)]]
theorem admission008_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1007028616010970377992005024297334377/1666641098795744720060416000000000000000:ℝ) admission008_08_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission008_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_08_coefficients]
def admission008_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5703219133484380489599502474426888832/32741306980813611474609375:ℝ),(3391487248792188235769719517456801792/6548261396162722294921875:ℝ),(5601798623860564103367416933144068096/10913768993604537158203125:ℝ),(1110235808721680125144582578432376832/6548261396162722294921875:ℝ)],
![(2194549723260654795718347039790525616/6548261396162722294921875:ℝ),(6523517873264360822162959546900519936/6548261396162722294921875:ℝ),(2154485808742801420521552116138377216/2182753798720907431640625:ℝ),(2134489389597720664705933246178787328/6548261396162722294921875:ℝ)],
![(5269529482818893488992232724525739248/32741306980813611474609375:ℝ),(3132030624472172586393240029443718144/6548261396162722294921875:ℝ),(5170630419853442999240343647547817984/10913768993604537158203125:ℝ),(1024253580876040539561350667746410496/6548261396162722294921875:ℝ)]]
theorem admission008_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (30525135424019114362041672103/3051710996330098974720000000000:ℝ) admission008_09_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission008_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_09_coefficients]
def admission008_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3251904448759616615281381888/69253807763671875:ℝ),(1930849384574725250287430144/13850761552734375:ℝ),(308157126445992513979088896/2233993798828125:ℝ),(101629954315943816038580224/2233993798828125:ℝ)],
![(6249821975878781270060268928/69253807763671875:ℝ),(18548322802576621114535800192/69253807763671875:ℝ),(733894284144580890325663744/2770152310546875:ℝ),(6048856554898557413666062336/69253807763671875:ℝ)],
![(332886716215534147857370952/7694867529296875:ℝ),(197517351163900328772472232/1538973505859375:ℝ),(976523027365961825667134464/7694867529296875:ℝ),(321823003307033392162144256/7694867529296875:ℝ)]]
theorem admission008_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (22097831953150181041407/8262301096345600000000000:ℝ) admission008_10_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission008_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_10_coefficients]
def admission008_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34351219426168630769552028345499648/10477218233860355671875:ℝ),(34258939685132431258208934344065024/3492406077953451890625:ℝ),(1102153792906326486690661100683264/112658260579143609375:ℝ),(34074703111059700257156707676848128/10477218233860355671875:ℝ)],
![(68177417347589610937910636201418752/10477218233860355671875:ℝ),(67993586594079097780623120131612672/3492406077953451890625:ℝ),(67809970237651746804272611104653312/3492406077953451890625:ℝ),(67626568278307558008859109120540672/10477218233860355671875:ℝ)],
![(33826197921420980168358607855919104/10477218233860355671875:ℝ),(33734646908946666522414185787547648/3492406077953451890625:ℝ),(33643202657555625716862116983472128/3492406077953451890625:ℝ),(33551865167247857751702401443692544/10477218233860355671875:ℝ)]]
theorem admission008_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (124990437802850670187556749/610342199266019794944000000:ℝ) admission008_11_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission008_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_11_coefficients]
def admission008_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(56532899009495302144/439453125:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/439453125:ℝ)],
![(113065798018990604288/439453125:ℝ),(113065798018990604288/146484375:ℝ),(113065798018990604288/146484375:ℝ),(113065798018990604288/439453125:ℝ)],
![(56532899009495302144/439453125:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/439453125:ℝ)]]
theorem admission008_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission008_12_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission008_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_12_coefficients]
def admission008_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17904005385842252054528/274658203125:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/274658203125:ℝ)],
![(35808010771684504109056/274658203125:ℝ),(35808010771684504109056/91552734375:ℝ),(35808010771684504109056/91552734375:ℝ),(35808010771684504109056/274658203125:ℝ)],
![(17904005385842252054528/274658203125:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/274658203125:ℝ)]]
theorem admission008_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission008_13_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission008_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_13_coefficients]
def admission008_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)],
![(140737488355328/9:ℝ),(140737488355328/3:ℝ),(140737488355328/3:ℝ),(140737488355328/9:ℝ)],
![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)]]
theorem admission008_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission008_14_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission008_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_14_coefficients]
theorem admission008_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission008_00_pos hd hp
 · exact admission008_01_pos hd hp
 · exact admission008_02_pos hd hp
 · exact admission008_03_pos hd hp
 · exact admission008_04_pos hd hp
 · exact admission008_05_pos hd hp
 · exact admission008_06_pos hd hp
 · exact admission008_07_pos hd hp
 · exact admission008_08_pos hd hp
 · exact admission008_09_pos hd hp
 · exact admission008_10_pos hd hp
 · exact admission008_11_pos hd hp
 · exact admission008_12_pos hd hp
 · exact admission008_13_pos hd hp
 · exact admission008_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission008_all
