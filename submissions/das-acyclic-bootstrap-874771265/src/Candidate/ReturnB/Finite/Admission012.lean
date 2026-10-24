/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission012_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)],
![(1740282940120050434048/472772661:ℝ),(15613399543800049696768/1418317983:ℝ),(15564252626519645487104/1418317983:ℝ),(5171701903079747092480/1418317983:ℝ)],
![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)]]
theorem admission012_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission012_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission012_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_00_coefficients]
def admission012_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)],
![(3813005592269877673984/1418317983:ℝ),(11411528986115233021952/1418317983:ℝ),(11384041195420833021952/1418317983:ℝ),(420613089063941963776/157590887:ℝ)],
![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)]]
theorem admission012_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission012_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission012_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_01_coefficients]
def admission012_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)],
![(30295193123274185240477696/22161218484375:ℝ),(6045257608730250556997632/1477414565625:ℝ),(30157382964028320329498624/7387072828125:ℝ),(30088477884405387874009088/22161218484375:ℝ)],
![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)]]
theorem admission012_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission012_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission012_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_02_coefficients]
def admission012_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1434371220621500612608/1418317983:ℝ),(12851731270859365548032/4254953949:ℝ),(12794194694301225582592/4254953949:ℝ),(4245577085306361872384/4254953949:ℝ)],
![(2859127782120183824384/1418317983:ℝ),(25616955280141544587264/4254953949:ℝ),(25501907269412634755072/4254953949:ℝ),(8462335335631641640960/4254953949:ℝ)],
![(1424756561498683211776/1418317983:ℝ),(12765224009282179039232/4254953949:ℝ),(12707712575111409172480/4254953949:ℝ),(4216758250325279768576/4254953949:ℝ)]]
theorem admission012_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (245447634389/484119204864:ℝ) admission012_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission012_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_03_coefficients]
def admission012_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7511460095952559058944/47658534375:ℝ),(894733828394971574272/1906341375:ℝ),(22202705409919139446784/47658534375:ℝ),(7345819795997409148928/47658534375:ℝ)],
![(2343409909637243276480512/7387072828125:ℝ),(6978592975158896217411584/7387072828125:ℝ),(6927078841872844595396608/7387072828125:ℝ),(763965258783730551488512/2462357609375:ℝ)],
![(1179133594764596622344192/7387072828125:ℝ),(1170499796709460455702528/2462357609375:ℝ),(1161886501111792660381696/2462357609375:ℝ),(1153293707971593236381696/7387072828125:ℝ)]]
theorem admission012_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656767469286687/8328932556800000:ℝ) admission012_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission012_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_04_coefficients]
def admission012_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2131312357461126689927168/22161218484375:ℝ),(6396160506812001357328384/22161218484375:ℝ),(6398295795864692016717824/22161218484375:ℝ),(711149215504605783105536/7387072828125:ℝ)],
![(836102127190555481083904/4432243696875:ℝ),(12546508990683846348886016/22161218484375:ℝ),(12551309214077654511468544/22161218484375:ℝ),(15001114191206399885312/79430890625:ℝ)],
![(2049198278491650715492352/22161218484375:ℝ),(6150348483871844991557632/22161218484375:ℝ),(1230602683642592498950144/4432243696875:ℝ),(136790880855517881245696/1477414565625:ℝ)]]
theorem admission012_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (250146274229937831481/5287872701661184000000:ℝ) admission012_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission012_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_05_coefficients]
def admission012_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17834824279546365026703282912456704/77531414930566631971875:ℝ),(3523427822955559765586199441281024/5168760995371108798125:ℝ),(52201612138723765194475617308901376/77531414930566631971875:ℝ),(1145667640289114596465727240142848/5168760995371108798125:ℝ)],
![(179384599103258712746773467399385088/387657074652833159859375:ℝ),(35440667165504435127433064948043776/25843804976855543990625:ℝ),(525098790442045456184643520804421632/387657074652833159859375:ℝ),(11524889148170456565168067598876672/25843804976855543990625:ℝ)],
![(90210477705526887613257052837101568/387657074652833159859375:ℝ),(17823528050726636299502067741638656/25843804976855543990625:ℝ),(264090729748426630212265434259914752/387657074652833159859375:ℝ),(5796550946724883582839431398162432/25843804976855543990625:ℝ)]]
theorem admission012_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (34143556365046340121797539/301102151637903098839040000:ℝ) admission012_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission012_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_06_coefficients]
def admission012_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(343537561372569271685579014303744/698481215590690378125:ℝ),(3075295438071664811930583208251392/2095443646772071134375:ℝ),(3058785674513759412523443184205824/2095443646772071134375:ℝ),(1014102920559802415649597018865664/2095443646772071134375:ℝ)],
![(3409248997696110562370911658831872/3492406077953451890625:ℝ),(244147630572411274216055805841408/83817745870882845375:ℝ),(30353993902161287251153018666614784/10477218233860355671875:ℝ),(402531482947928386450351116517376/419088729354414226875:ℝ)],
![(1691561190833264203943016587313152/3492406077953451890625:ℝ),(3028395326238617043470811937783808/2095443646772071134375:ℝ),(15060065529592490188535802745585664/10477218233860355671875:ℝ),(998554494179839516602158563721216/2095443646772071134375:ℝ)]]
theorem admission012_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (7439810739307399962858547/30517109963300989747200000:ℝ) admission012_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission012_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_07_coefficients]
def admission012_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2701120751062580879349244480277269376/818532674520340286865234375:ℝ),(14294373216175056732806797788245672528/1364221124200567144775390625:ℝ),(45246776346755506792007776107017536384/4092663372601701434326171875:ℝ),(3173843443362938018885717539422123136/818532674520340286865234375:ℝ)],
![(166220985546280455039235863256371923968/20463316863008507171630859375:ℝ),(173916347910919697190828612313599869264/6821105621002835723876953125:ℝ),(544810940588661064400372212441711293184/20463316863008507171630859375:ℝ),(37856489728032747969382767584495471872/4092663372601701434326171875:ℝ)],
![(98692966769715933055504751249440189568/20463316863008507171630859375:ℝ),(102444481830044413526794623372371506624/6821105621002835723876953125:ℝ),(318577058854883530440333331906623611264/20463316863008507171630859375:ℝ),(21987272511218057874954179887384856192/4092663372601701434326171875:ℝ)]]
theorem admission012_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (21102505867676413119915972502166167/12499808240968085400453120000000000000:ℝ) admission012_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission012_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_08_coefficients]
def admission012_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(129700977230355623630822807146019216/6548261396162722294921875:ℝ),(382043909471768186562931920953465344/6548261396162722294921875:ℝ),(125000227664922290796804981274574848/2182753798720907431640625:ℝ),(122657808369152593346216839050428416/6548261396162722294921875:ℝ)],
![(1242324421836292272036372021573293072/32741306980813611474609375:ℝ),(117978489119927425013231309205165568/1056171192929471337890625:ℝ),(1195949118050967372925801435525414912/10913768993604537158203125:ℝ),(46913567651520047698905937853022208/1309652279232544458984375:ℝ)],
![(593819535684514153882257985843196992/32741306980813611474609375:ℝ),(1747113615358909242595510980592805888/32741306980813611474609375:ℝ),(570947979726355918941776529152540672/10913768993604537158203125:ℝ),(111910029888447645148312850214682624/6548261396162722294921875:ℝ)]]
theorem admission012_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (6670357578304269620675614489/762927749082524743680000000000:ℝ) admission012_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission012_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_09_coefficients]
def admission012_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(370156186261179935135826148/69253807763671875:ℝ),(362146918786071940330486348/23084602587890625:ℝ),(1062452708103599529054502144/69253807763671875:ℝ),(346168281593477705698869248/69253807763671875:ℝ)],
![(706874909713613459605215136/69253807763671875:ℝ),(691014197292164904964282336/23084602587890625:ℝ),(2025538173731280328836548608/69253807763671875:ℝ),(659370780594961573548916736/69253807763671875:ℝ)],
![(37386062692296287167275584/7694867529296875:ℝ),(109541490288801481832940096/7694867529296875:ℝ),(64157405617118719764312064/4616920517578125:ℝ),(104320793777953014824566784/23084602587890625:ℝ)]]
theorem admission012_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1193856740317760637183/516393818521600000000000:ℝ) admission012_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission012_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_10_coefficients]
def admission012_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4228875940930648498732214692573184/10477218233860355671875:ℝ),(4206300046467993099901569024118784/3492406077953451890625:ℝ),(4183776657630357621114799473557504/3492406077953451890625:ℝ),(4161305774417742062371906040889344/10477218233860355671875:ℝ)],
![(8391850592463402285233637156204544/10477218233860355671875:ℝ),(1669376284627374240799632811937792/698481215590690378125:ℝ),(8302016827602071712774292941832192/3492406077953451890625:ℝ),(1651451361171800762312404760526848/2095443646772071134375:ℝ)],
![(832594930306550757300284492726272/2095443646772071134375:ℝ),(4140581376668878104096595035570176/3492406077953451890625:ℝ),(4118240169971714091659493468274688/3492406077953451890625:ℝ),(4095951031441261749190117761744896/10477218233860355671875:ℝ)]]
theorem admission012_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (30517213280806405463741107/152585549816504948736000000:ℝ) admission012_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission012_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_11_coefficients]
def admission012_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)],
![(14133224752373825536/439453125:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/439453125:ℝ)],
![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)]]
theorem admission012_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission012_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission012_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_12_coefficients]
def admission012_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)],
![(4476001346460563013632/274658203125:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/274658203125:ℝ)],
![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)]]
theorem admission012_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission012_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission012_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_13_coefficients]
def admission012_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission012_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission012_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission012_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_14_coefficients]
theorem admission012_all {δ p : ℝ}
 (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission012_00_pos hd hp
 · exact admission012_01_pos hd hp
 · exact admission012_02_pos hd hp
 · exact admission012_03_pos hd hp
 · exact admission012_04_pos hd hp
 · exact admission012_05_pos hd hp
 · exact admission012_06_pos hd hp
 · exact admission012_07_pos hd hp
 · exact admission012_08_pos hd hp
 · exact admission012_09_pos hd hp
 · exact admission012_10_pos hd hp
 · exact admission012_11_pos hd hp
 · exact admission012_12_pos hd hp
 · exact admission012_13_pos hd hp
 · exact admission012_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission012_all
