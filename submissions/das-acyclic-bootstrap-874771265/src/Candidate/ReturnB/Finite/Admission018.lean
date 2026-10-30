/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission018_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10624991406533378048/45752193:ℝ),(981980836147553632256/1418317983:ℝ),(975837471487503106048/1418317983:ℝ),(323231368942484193280/1418317983:ℝ)],
![(21249982813066756096/45752193:ℝ),(1963961672295107264512/1418317983:ℝ),(1951674942975006212096/1418317983:ℝ),(646462737884968386560/1418317983:ℝ)],
![(10624991406533378048/45752193:ℝ),(981980836147553632256/1418317983:ℝ),(975837471487503106048/1418317983:ℝ),(323231368942484193280/1418317983:ℝ)]]
theorem admission018_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission018_00_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission018_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_00_coefficients]
def admission018_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7742930207589269504/45752193:ℝ),(716656535469002063872/1418317983:ℝ),(713220561632202063872/1418317983:ℝ),(26288318066496372736/157590887:ℝ)],
![(15485860415178539008/45752193:ℝ),(1433313070938004127744/1418317983:ℝ),(1426441123264404127744/1418317983:ℝ),(52576636132992745472/157590887:ℝ)],
![(7742930207589269504/45752193:ℝ),(716656535469002063872/1418317983:ℝ),(713220561632202063872/1418317983:ℝ),(26288318066496372736/157590887:ℝ)]]
theorem admission018_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission018_01_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission018_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_01_coefficients]
def admission018_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(61495782988191497191424/714878015625:ℝ),(1897756137681069855997952/7387072828125:ℝ),(377828600545640659812352/1477414565625:ℝ),(1880529867775336742125568/22161218484375:ℝ)],
![(122991565976382994382848/714878015625:ℝ),(3795512275362139711995904/7387072828125:ℝ),(755657201091281319624704/1477414565625:ℝ),(3761059735550673484251136/22161218484375:ℝ)],
![(61495782988191497191424/714878015625:ℝ),(1897756137681069855997952/7387072828125:ℝ),(377828600545640659812352/1477414565625:ℝ),(1880529867775336742125568/22161218484375:ℝ)]]
theorem admission018_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission018_02_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission018_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_02_coefficients]
def admission018_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(537870185073389600768/4254953949:ℝ),(1599195284258403909632/4254953949:ℝ),(1584817526103039016960/4254953949:ℝ),(523492426918024708096/4254953949:ℝ)],
![(1072131848142101413888/4254953949:ℝ),(102824868845329580032/137256579:ℝ),(3158821585526529720320/4254953949:ℝ),(33657499982690779136/137256579:ℝ)],
![(534261663068711813120/4254953949:ℝ),(1588375649946813071360/4254953949:ℝ),(1574004059423490703360/4254953949:ℝ),(519890072545389445120/4254953949:ℝ)]]
theorem admission018_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (30261585055/60514900608:ℝ) admission018_03_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission018_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_03_coefficients]
def admission018_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(50866014306762724227072/2462357609375:ℝ),(150387636394259979450368/2462357609375:ℝ),(148187678235980090834944/2462357609375:ℝ),(48666056148482835611648/2462357609375:ℝ)],
![(307074049434071544604672/7387072828125:ℝ),(907918003362535508518912/7387072828125:ℝ),(178935349153672065974272/1477414565625:ℝ),(58766558367979273191424/1477414565625:ℝ)],
![(154476006513783371923456/7387072828125:ℝ),(14734035296121147424768/238292671875:ℝ),(450113711060420057366528/7387072828125:ℝ),(147834623394447859122176/7387072828125:ℝ)]]
theorem admission018_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (104426027616583233/1290984546304000000:ℝ) admission018_04_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission018_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_04_coefficients]
def admission018_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5458700654577012156416/492471521875:ℝ),(738055870990978262075392/22161218484375:ℝ),(739141943566405141495808/22161218484375:ℝ),(246727602031392426459136/22161218484375:ℝ)],
![(32063496747315470891008/1477414565625:ℝ),(1445252756707349678262272/22161218484375:ℝ),(1447557455350271326486528/22161218484375:ℝ),(483257149852653711589376/22161218484375:ℝ)],
![(3137478956716886884352/295482913125:ℝ),(141439377143274283237376/4432243696875:ℝ),(141683102356773236998144/4432243696875:ℝ),(47305909564252257026048/4432243696875:ℝ)]]
theorem admission018_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (287244777531453267/6609840877076480000:ℝ) admission018_05_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission018_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_05_coefficients]
def admission018_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1313999100635919647914844784490496/43073008294759239984375:ℝ),(34640138750397186171995881002285056/387657074652833159859375:ℝ),(33810601691904429940143952808640512/387657074652833159859375:ℝ),(733095461500524272918778324451328/25843804976855543990625:ℝ)],
![(2642576829547619865493212368336896/43073008294759239984375:ℝ),(69670556685202873388704340146763776/387657074652833159859375:ℝ),(68008173955314688812386519560486912/387657074652833159859375:ℝ),(294943503232192474180281209716736/5168760995371108798125:ℝ)],
![(53143109156468008703134703353856/1722920331790369599375:ℝ),(7006083586961137443341691828895744/77531414930566631971875:ℝ),(1367902890536410354889702670073856/15506282986113326394375:ℝ),(741622054660438097982627724132352/25843804976855543990625:ℝ)]]
theorem admission018_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (174783578276759212712950307/1505510758189515494195200000:ℝ) admission018_06_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission018_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_06_coefficients]
def admission018_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(550232502277316244107705952256/9086919543677671875:ℝ),(1883135353641668219998063909906432/10477218233860355671875:ℝ),(1863096070890845476513579014815744/10477218233860355671875:ℝ),(122875758474984577194340013572096/2095443646772071134375:ℝ)],
![(1258958637488764309991458390059008/10477218233860355671875:ℝ),(3736798549726440020173459127969792/10477218233860355671875:ℝ),(3696879730500044670220751839166464/10477218233860355671875:ℝ),(243807963652473792007750220251136/2095443646772071134375:ℝ)],
![(124908112472603736107054685421568/2095443646772071134375:ℝ),(370732639216954360035079043612672/2095443646772071134375:ℝ),(366756731921839838741434564870144/2095443646772071134375:ℝ),(24186441035497842962682041335808/419088729354414226875:ℝ)]]
theorem admission018_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (180203028287722490449861/762927749082524743680000:ℝ) admission018_07_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission018_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_07_coefficients]
def admission018_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5212261339657634342691598616343121292/6821105621002835723876953125:ℝ),(49293050481072733672676769802736225228/20463316863008507171630859375:ℝ),(51674105549290564348983407601679950356/20463316863008507171630859375:ℝ),(6005872441538420993407813646072279668/6821105621002835723876953125:ℝ)],
![(2349440141907861106068493134521003264/1364221124200567144775390625:ℝ),(22068957940470495697566550184636680544/4092663372601701434326171875:ℝ),(114962651701851313229554942689479682088/20463316863008507171630859375:ℝ),(13286339736077543607758458998451692776/6821105621002835723876953125:ℝ)],
![(6534939369881671187650867056261895028/6821105621002835723876953125:ℝ),(61051739221279744815155981120447177492/20463316863008507171630859375:ℝ),(63288546152560748880571535087799731732/20463316863008507171630859375:ℝ),(7280467294539122614350645352379413108/6821105621002835723876953125:ℝ)]]
theorem admission018_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1303065334914408585672899654085780323/416660274698936180015104000000000000000:ℝ) admission018_08_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission018_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_08_coefficients]
def admission018_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71099991623780345359685263994061968/32741306980813611474609375:ℝ),(205394375171690672028502072882818304/32741306980813611474609375:ℝ),(65840165054820513354512283100413952/10913768993604537158203125:ℝ),(12645281425967837118801107672367104/6548261396162722294921875:ℝ)],
![(135245091382011512899092500295576208/32741306980813611474609375:ℝ),(390163437589477023639732420441853184/32741306980813611474609375:ℝ),(124884402010517735572152464918085632/10913768993604537158203125:ℝ),(772486791672501797189168281944064/211234238585894267578125:ℝ)],
![(12829019951646233507881447260302848/6548261396162722294921875:ℝ),(36953812483557270322246069511806976/6548261396162722294921875:ℝ),(11808847391139444443528036363534336/2182753798720907431640625:ℝ),(2260361823175943718812621813579776/1309652279232544458984375:ℝ)]]
theorem admission018_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (134728063534256441522396911/19073193727063118592000000000:ℝ) admission018_09_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission018_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_09_coefficients]
def admission018_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(40426756979092342684547714/69253807763671875:ℝ),(12860769685118760424299314/7694867529296875:ℝ),(2449545551352750682136128/1538973505859375:ℝ),(34909530717373842061979648/69253807763671875:ℝ)],
![(5091079773491854154049152/4616920517578125:ℝ),(1745274619860753704447872/554030462109375:ℝ),(41450209547168006352351232/13850761552734375:ℝ),(4363881396208242067767296/4616920517578125:ℝ)],
![(1436336449071176418297856/2770152310546875:ℝ),(4092813416683331337095168/2770152310546875:ℝ),(3877217868304022360096768/2770152310546875:ℝ),(1220747020691867441299456/2770152310546875:ℝ)]]
theorem admission018_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (582097540231641503/322746136576000000000:ℝ) admission018_10_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission018_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_10_coefficients]
def admission018_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(451178315792497900560772519936/9086919543677671875:ℝ),(514721866195972486195089994074112/3492406077953451890625:ℝ),(509260512179088352913246817353728/3492406077953451890625:ℝ),(503824536058097679501041185325056/10477218233860355671875:ℝ)],
![(1032110888646355332226054215784448/10477218233860355671875:ℝ),(1021183298449649200067622461622272/3492406077953451890625:ℝ),(1010306245315575862610390668279808/3492406077953451890625:ℝ),(999479729244135319854358835757056/10477218233860355671875:ℝ)],
![(102380458107521050575896700059648/2095443646772071134375:ℝ),(101292286450735342774506493509632/698481215590690378125:ℝ),(100209146627297501939428770185216/698481215590690378125:ℝ),(3965241545488301122826541203456/83817745870882845375:ℝ)]]
theorem admission018_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (29543351720931389352877/152585549816504948736000:ℝ) admission018_11_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission018_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_11_coefficients]
def admission018_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(883326547023364096/439453125:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/439453125:ℝ)],
![(1766653094046728192/439453125:ℝ),(1766653094046728192/146484375:ℝ),(1766653094046728192/146484375:ℝ),(1766653094046728192/439453125:ℝ)],
![(883326547023364096/439453125:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/439453125:ℝ)]]
theorem admission018_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission018_12_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission018_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_12_coefficients]
def admission018_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(279750084153785188352/274658203125:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/274658203125:ℝ)],
![(559500168307570376704/274658203125:ℝ),(559500168307570376704/91552734375:ℝ),(559500168307570376704/91552734375:ℝ),(559500168307570376704/274658203125:ℝ)],
![(279750084153785188352/274658203125:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/274658203125:ℝ)]]
theorem admission018_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission018_13_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission018_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_13_coefficients]
def admission018_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)],
![(2199023255552/9:ℝ),(2199023255552/3:ℝ),(2199023255552/3:ℝ),(2199023255552/9:ℝ)],
![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)]]
theorem admission018_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission018_14_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission018_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_14_coefficients]
theorem admission018_all {δ p : ℝ}
 (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission018_00_pos hd hp
 · exact admission018_01_pos hd hp
 · exact admission018_02_pos hd hp
 · exact admission018_03_pos hd hp
 · exact admission018_04_pos hd hp
 · exact admission018_05_pos hd hp
 · exact admission018_06_pos hd hp
 · exact admission018_07_pos hd hp
 · exact admission018_08_pos hd hp
 · exact admission018_09_pos hd hp
 · exact admission018_10_pos hd hp
 · exact admission018_11_pos hd hp
 · exact admission018_12_pos hd hp
 · exact admission018_13_pos hd hp
 · exact admission018_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission018_all
