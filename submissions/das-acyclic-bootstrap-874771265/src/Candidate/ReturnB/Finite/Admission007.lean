/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission007_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)],
![(1740282940120050434048/472772661:ℝ),(15613399543800049696768/1418317983:ℝ),(15564252626519645487104/1418317983:ℝ),(5171701903079747092480/1418317983:ℝ)],
![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)]]
theorem admission007_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission007_00_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission007_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_00_coefficients]
def admission007_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)],
![(3813005592269877673984/1418317983:ℝ),(11411528986115233021952/1418317983:ℝ),(11384041195420833021952/1418317983:ℝ),(420613089063941963776/157590887:ℝ)],
![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)]]
theorem admission007_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission007_01_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission007_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_01_coefficients]
def admission007_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)],
![(30295193123274185240477696/22161218484375:ℝ),(6045257608730250556997632/1477414565625:ℝ),(30157382964028320329498624/7387072828125:ℝ),(30088477884405387874009088/22161218484375:ℝ)],
![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)]]
theorem admission007_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission007_02_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission007_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_02_coefficients]
def admission007_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1448805780499411763200/1418317983:ℝ),(12981568298176055607296/4254953949:ℝ),(12923956294455805345792/4254953949:ℝ),(4288805337777985028096/4254953949:ℝ)],
![(2887996901876006125568/1418317983:ℝ),(25876629334774924705792/4254953949:ℝ),(25761430469721794281472/4254953949:ℝ),(8548791840574887952384/4254953949:ℝ)],
![(1439191121376594362368/1418317983:ℝ),(12895061036598869098496/4254953949:ℝ),(12837474175265988935680/4254953949:ℝ),(4259986502796902924288/4254953949:ℝ)]]
theorem admission007_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (991855399403/1936476819456:ℝ) admission007_03_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission007_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_03_coefficients]
def admission007_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1141741934584788976959488/7387072828125:ℝ),(135999541916035679289344/295482913125:ℝ),(3374811222307709195911168/7387072828125:ℝ),(1116564608991606190637056/7387072828125:ℝ)],
![(2298341149061527922126848/7387072828125:ℝ),(6844382900899650481270784/7387072828125:ℝ),(6793862609413329758715904/7387072828125:ℝ),(749273619191735733190656/2462357609375:ℝ)],
![(231319842895347789033472/1477414565625:ℝ),(1148131450999586166345728/2462357609375:ℝ),(1139683795701873520934912/2462357609375:ℝ),(1131256248583601008934912/7387072828125:ℝ)]]
theorem admission007_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478581916447053/161373068288000000:ℝ) admission007_04_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission007_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_04_coefficients]
def admission007_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(72725273416623891986432/714878015625:ℝ),(6764083220269828569683968/22161218484375:ℝ),(6764629573457238697662464/22161218484375:ℝ),(751676609700916926519296/7387072828125:ℝ)],
![(4426852872861205328723968/22161218484375:ℝ),(13282354417599500773597184/22161218484375:ℝ),(13283976769262747873357824/22161218484375:ℝ),(492052802724939158720512/2462357609375:ℝ)],
![(2172369396945864677144576/22161218484375:ℝ),(6518271197329672203913216/22161218484375:ℝ),(1303869439161101835139072/4432243696875:ℝ),(144896359694780109928448/1477414565625:ℝ)]]
theorem admission007_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (1060727244602472986887/21151490806644736000000:ℝ) admission007_05_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission007_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_05_coefficients]
def admission007_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(87599839243131126205787391680413696/387657074652833159859375:ℝ),(17304929660688184115516363989221376/25843804976855543990625:ℝ),(256364413835548878787194719226036224/387657074652833159859375:ℝ),(5626019083526607081562443404541952/25843804976855543990625:ℝ)],
![(952627215103012512926029306138624/2095443646772071134375:ℝ),(34816248257325205702603798513676288/25843804976855543990625:ℝ),(103162299345181112362855357233496064/77531414930566631971875:ℝ),(11320250912332524763635682006532096/25843804976855543990625:ℝ)],
![(88636195550926188685528029955231744/387657074652833159859375:ℝ),(17511318596637021587087434524454912/25843804976855543990625:ℝ),(259447082890356683027082066941444096/387657074652833159859375:ℝ),(5694231828805917682073238601990144/25843804976855543990625:ℝ)]]
theorem admission007_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (20958554310823258316376967/188188844773689436774400000:ℝ) admission007_06_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission007_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_06_coefficients]
def admission007_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1757196589001685574263934386274304/3492406077953451890625:ℝ),(3146027854860975071596423971504128/2095443646772071134375:ℝ),(15645677307948552456294090206609408/10477218233860355671875:ℝ),(1037425560129746764220754701582336/2095443646772071134375:ℝ)],
![(697653312394757798808598057668608/698481215590690378125:ℝ),(6245155597888902374733076672540672/2095443646772071134375:ℝ),(6211498354584159607701353447555072/2095443646772071134375:ℝ),(2059302693879530629394070948020224/2095443646772071134375:ℝ)],
![(1731069972972103419779055902068736/3492406077953451890625:ℝ),(3099127743027927303136652701036544/2095443646772071134375:ℝ),(15411814464972245582212677031165952/10477218233860355671875:ℝ),(1021877133749783865173316246437888/2095443646772071134375:ℝ)]]
theorem admission007_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (30454311780625100886026509/122068439853203958988800000:ℝ) admission007_07_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission007_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_07_coefficients]
def admission007_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20780596786837405376070653143169051648/20463316863008507171630859375:ℝ),(5060288164619002136682508902312322688/1364221124200567144775390625:ℝ),(89446616339640894342136903011767942144/20463316863008507171630859375:ℝ),(34322678657750050371919514495202153472/20463316863008507171630859375:ℝ)],
![(72726141566826221823914945528846558464/20463316863008507171630859375:ℝ),(81575497395359151229585723454266370864/6821105621002835723876953125:ℝ),(271236409800387785164568257395071813632/20463316863008507171630859375:ℝ),(99235633787516939646466989941775509504/20463316863008507171630859375:ℝ)],
![(51945544779988816447844292385677506816/20463316863008507171630859375:ℝ),(56274056572264140546173178942704757424/6821105621002835723876953125:ℝ),(181789793460746890822431354383303871488/20463316863008507171630859375:ℝ),(64912955129766889274547475446573356032/20463316863008507171630859375:ℝ)]]
theorem admission007_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (20293551549645903687568997210126027/39061900753025266876416000000000000000:ℝ) admission007_08_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission007_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_08_coefficients]
def admission007_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(731952598948282899485402269122699904/32741306980813611474609375:ℝ),(2157712327542774669019265728486608896/32741306980813611474609375:ℝ),(22792008887551320891177100702121984/352057064309823779296875:ℝ),(138779476090210015643072822304047104/6548261396162722294921875:ℝ)],
![(281843969485860366939789697671700144/6548261396162722294921875:ℝ),(830463744617123529563876566559739392/6548261396162722294921875:ℝ),(271810278485985272042146373262245888/2182753798720907431640625:ℝ),(266811173699715083088241655772348416/6548261396162722294921875:ℝ)],
![(677267248481018935213546219235800816/32741306980813611474609375:ℝ),(1994606395542842978800117104312088064/32741306980813611474609375:ℝ),(652499116915835412584241744545447936/10913768993604537158203125:ℝ),(128031697609505067445168833468301312/6548261396162722294921875:ℝ)]]
theorem admission007_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (30525135424019114362041672103/3051710996330098974720000000000:ℝ) admission007_09_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission007_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_09_coefficients]
def admission007_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(419182644304963185751247104/69253807763671875:ℝ),(410712073482258673497064192/23084602587890625:ℝ),(7785609748603839496060928/446798759765625:ℝ),(12703744289492977004822528/2233993798828125:ℝ)],
![(5202534071817945810448448/446798759765625:ℝ),(789601352522669486107292224/23084602587890625:ℝ),(2318518067816671534410625024/69253807763671875:ℝ),(756107069362319676708257792/69253807763671875:ℝ)],
![(42996219733894608322705956/7694867529296875:ℝ),(4071467434416368747045724/248221533203125:ℝ),(24689426120270586871195904/1538973505859375:ℝ),(40227875413379174020268032/7694867529296875:ℝ)]]
theorem admission007_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (22097831953150181041407/8262301096345600000000000:ℝ) admission007_10_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission007_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_10_coefficients]
def admission007_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4328547694659612165651908960681984/10477218233860355671875:ℝ),(4305423941400617617543808571047936/3492406077953451890625:ℝ),(856470801228313547941607014137856/698481215590690378125:ℝ),(4259337888882462532144588459606016/10477218233860355671875:ℝ)],
![(8591194099921329619073025692422144/10477218233860355671875:ℝ),(8545129213002120239282643153547264/3492406077953451890625:ℝ),(8499171524624491949960764136095744/3492406077953451890625:ℝ),(8453321034788444751107388640067584/10477218233860355671875:ℝ)],
![(852529281052343490684223346348032/2095443646772071134375:ℝ),(4239705271601502621738834582499328/3492406077953451890625:ℝ),(4216817518482924210252729065406464/3492406077953451890625:ℝ),(4193983145905982218962800180461568/10477218233860355671875:ℝ)]]
theorem admission007_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (124990437802850670187556749/610342199266019794944000000:ℝ) admission007_11_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission007_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_11_coefficients]
def admission007_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)],
![(14133224752373825536/439453125:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/439453125:ℝ)],
![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)]]
theorem admission007_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission007_12_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission007_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_12_coefficients]
def admission007_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)],
![(4476001346460563013632/274658203125:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/274658203125:ℝ)],
![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)]]
theorem admission007_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission007_13_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission007_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_13_coefficients]
def admission007_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission007_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission007_14_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission007_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_14_coefficients]
theorem admission007_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission007_00_pos hd hp
 · exact admission007_01_pos hd hp
 · exact admission007_02_pos hd hp
 · exact admission007_03_pos hd hp
 · exact admission007_04_pos hd hp
 · exact admission007_05_pos hd hp
 · exact admission007_06_pos hd hp
 · exact admission007_07_pos hd hp
 · exact admission007_08_pos hd hp
 · exact admission007_09_pos hd hp
 · exact admission007_10_pos hd hp
 · exact admission007_11_pos hd hp
 · exact admission007_12_pos hd hp
 · exact admission007_13_pos hd hp
 · exact admission007_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission007_all
