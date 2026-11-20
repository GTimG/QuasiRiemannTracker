/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission017_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3480565880240100868096/472772661:ℝ),(31226799087600099393536/1418317983:ℝ),(31128505253039290974208/1418317983:ℝ),(10343403806159494184960/1418317983:ℝ)],
![(6961131760480201736192/472772661:ℝ),(62453598175200198787072/1418317983:ℝ),(62257010506078581948416/1418317983:ℝ),(20686807612318988369920/1418317983:ℝ)],
![(3480565880240100868096/472772661:ℝ),(31226799087600099393536/1418317983:ℝ),(31128505253039290974208/1418317983:ℝ),(10343403806159494184960/1418317983:ℝ)]]
theorem admission017_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission017_00_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission017_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_00_coefficients]
def admission017_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7626011184539755347968/1418317983:ℝ),(22823057972230466043904/1418317983:ℝ),(22768082390841666043904/1418317983:ℝ),(841226178127883927552/157590887:ℝ)],
![(15252022369079510695936/1418317983:ℝ),(45646115944460932087808/1418317983:ℝ),(45536164781683332087808/1418317983:ℝ),(1682452356255767855104/157590887:ℝ)],
![(7626011184539755347968/1418317983:ℝ),(22823057972230466043904/1418317983:ℝ),(22768082390841666043904/1418317983:ℝ),(841226178127883927552/157590887:ℝ)]]
theorem admission017_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission017_01_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission017_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_01_coefficients]
def admission017_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60590386246548370480955392/22161218484375:ℝ),(12090515217460501113995264/1477414565625:ℝ),(60314765928056640658997248/7387072828125:ℝ),(60176955768810775748018176/22161218484375:ℝ)],
![(121180772493096740961910784/22161218484375:ℝ),(24181030434921002227990528/1477414565625:ℝ),(120629531856113281317994496/7387072828125:ℝ),(120353911537621551496036352/22161218484375:ℝ)],
![(60590386246548370480955392/22161218484375:ℝ),(12090515217460501113995264/1477414565625:ℝ),(60314765928056640658997248/7387072828125:ℝ),(60176955768810775748018176/22161218484375:ℝ)]]
theorem admission017_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission017_02_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission017_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_02_coefficients]
def admission017_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5660517324728723046400/1418317983:ℝ),(50714562451016328937472/4254953949:ℝ),(50484768138206950457344/4254953949:ℝ),(16751757661376790659072/4254953949:ℝ)],
![(11301805331211811291136/1418317983:ℝ),(101256110378878284857344/4254953949:ℝ),(100796572038034268094464/4254953949:ℝ),(33445877652791417110528/4254953949:ℝ)],
![(5641288006483088244736/1418317983:ℝ),(50541547927861955919872/4254953949:ℝ),(50311803899827317637120/4254953949:ℝ),(538519999723052466176/137256579:ℝ)]]
theorem admission017_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (31345989539/62466994176:ℝ) admission017_03_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission017_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_03_coefficients]
def admission017_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4762265700833922443370496/7387072828125:ℝ),(567261247202411978088448/295482913125:ℝ),(14076515229888734409261056/7387072828125:ℝ),(4657249750662357400420352/7387072828125:ℝ)],
![(9554245961451744823156736/7387072828125:ℝ),(28451873970316331938029568/7387072828125:ℝ),(28241510789373291552309248/7387072828125:ℝ),(3114627593502901479145472/2462357609375:ℝ)],
![(958396052123564475957248/1477414565625:ℝ),(4756780930085344161939456/2462357609375:ℝ),(4721665186494852381016064/2462357609375:ℝ),(4686633029846347037016064/7387072828125:ℝ)]]
theorem admission017_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (208195287763879779/2581969092608000000:ℝ) admission017_04_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission017_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_04_coefficients]
def admission017_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7868336798088698964230144/22161218484375:ℝ),(23621327127536383848349696/22161218484375:ℝ),(23637283317785122299158528/22161218484375:ℝ),(876032554259715268337664/2462357609375:ℝ)],
![(15572445438238445979590656/22161218484375:ℝ),(46751030209192454965157888/22161218484375:ℝ),(46784001880266785554382848/22161218484375:ℝ),(5201805703104258856271872/7387072828125:ℝ)],
![(7704108640149747015360512/22161218484375:ℝ),(23129703081656071116808192/22161218484375:ℝ),(4629343712496332651044864/4432243696875:ℝ),(514741608065022610251776/1477414565625:ℝ)]]
theorem admission017_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (940442949237029664961/21151490806644736000000:ℝ) admission017_05_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission017_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_05_coefficients]
def admission017_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(364043135645730562196801098364526592/387657074652833159859375:ℝ),(71925533911529397302992277172477952/25843804976855543990625:ℝ),(1065702594778801724087034726997557248/387657074652833159859375:ℝ),(23390842022737466132890111184994304/25843804976855543990625:ℝ)],
![(4710703121980975802277957892120576/2501013384856988128125:ℝ),(144263845694956469549126695415422976/25843804976855543990625:ℝ),(427514105533443811330768829885186048/77531414930566631971875:ℝ),(46918109536033553466801812764884992/25843804976855543990625:ℝ)],
![(366115848261320687156282374914162688/387657074652833159859375:ℝ),(72338311783427072246134418242945024/25843804976855543990625:ℝ),(1071867932888417332566809422428372992/387657074652833159859375:ℝ),(23527267513296087333911701579890688/25843804976855543990625:ℝ)]]
theorem admission017_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (348550707440636547399909961/3011021516379030988390400000:ℝ) admission017_06_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission017_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_06_coefficients]
def admission017_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6660462866836864261397666058641408/3492406077953451890625:ℝ),(11924451861463322672139427239059456/2095443646772071134375:ℝ),(59300992062803552927598540190908416/10477218233860355671875:ℝ),(3932024271199506470218880434307072/2095443646772071134375:ℝ)],
![(2653734500322912842765115029774336/698481215590690378125:ℝ),(23755103499260549807359311937183744/2095443646772071134375:ℝ),(23626851687930898421406850806185984/2095443646772071134375:ℝ),(7832951689639087142342883958325248/2095443646772071134375:ℝ)],
![(6608209634777699952427909090230272/3492406077953451890625:ℝ),(11830651637797227135219884698124288/2095443646772071134375:ℝ),(58833266376850939179435713840021504/10477218233860355671875:ℝ),(3900927418439580672124003524018176/2095443646772071134375:ℝ)]]
theorem admission017_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (29064174133834098816841867/122068439853203958988800000:ℝ) admission017_07_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission017_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_07_coefficients]
def admission017_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(488266711058317965437339922725286123776/20463316863008507171630859375:ℝ),(100269889771961815046473872620671656032/1364221124200567144775390625:ℝ),(1543276098774414454057031417249176179968/20463316863008507171630859375:ℝ),(527493578992469669022947732563849963264/20463316863008507171630859375:ℝ)],
![(1038863318102938753018227123935589157888/20463316863008507171630859375:ℝ),(1064644129217956410190259995069002848288/6821105621002835723876953125:ℝ),(3271238551791040901074651737241424218624/20463316863008507171630859375:ℝ),(1116167710928973015851151387030442331648/20463316863008507171630859375:ℝ)],
![(550596607044620787580887201210303034112/20463316863008507171630859375:ℝ),(563294680358147334957890631965644568128/6821105621002835723876953125:ℝ),(1727962453016626447017620319992248038656/20463316863008507171630859375:ℝ),(588674131936503346828203654466592368384/20463316863008507171630859375:ℝ)]]
theorem admission017_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1907291840071554552489609073145648921/624990412048404270022656000000000000000:ℝ) admission017_08_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission017_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_08_coefficients]
def admission017_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2150857992486565418747591109576170848/32741306980813611474609375:ℝ),(6324695204699765406001916675843136512/32741306980813611474609375:ℝ),(2065693687344016771281742009479200768/10913768993604537158203125:ℝ),(404649005630970787801635445515747328/6548261396162722294921875:ℝ)],
![(838469056807720581790294023875708704/6548261396162722294921875:ℝ),(2464635709079933486313107220667446272/6548261396162722294921875:ℝ),(160931242299660898899159490580709376/436550759744181486328125:ℝ),(787802454300531679207462913360003072/6548261396162722294921875:ℝ)],
![(2041487291552037490203879009802372672/32741306980813611474609375:ℝ),(5998483340699902025563619427494094848/32741306980813611474609375:ℝ),(1957587370147505701197245255038533632/10913768993604537158203125:ℝ),(12359788666760028755026692511105024/211234238585894267578125:ℝ)]]
theorem admission017_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (736700812981130406560104639/98442290204196741120000000000:ℝ) admission017_09_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission017_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_09_coefficients]
def admission017_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1205534689436397661365001124/69253807763671875:ℝ),(1175773362460552392337815692/23084602587890625:ℝ),(687633885463911785800550656/13850761552734375:ℝ),(1116384629953088475854307328/69253807763671875:ℝ)],
![(15101782091293969947757456/446798759765625:ℝ),(2281588137405507565392590864/23084602587890625:ℝ),(6667463030494680353017478144/69253807763671875:ℝ),(2163476047375441748742111232/69253807763671875:ℝ)],
![(126110819499155637841499536/7694867529296875:ℝ),(368523989101755551306599824/7694867529296875:ℝ),(215237948120281428046490624/4616920517578125:ℝ),(348950433251576149837152256/23084602587890625:ℝ)]]
theorem admission017_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (15973683162761359398063/8262301096345600000000000:ℝ) admission017_10_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission017_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_10_coefficients]
def admission017_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16385014170010949902788497239973888/10477218233860355671875:ℝ),(16297267266543244337427369931661312/3492406077953451890625:ℝ),(3241944852231860590235128699027456/698481215590690378125:ℝ),(16122385153859125744033317930401792/10477218233860355671875:ℝ)],
![(32638225761226110381115410022064128/10477218233860355671875:ℝ),(32463097193488258683244791886225408/3492406077953451890625:ℝ),(32288375547001318843440674979708928/3492406077953451890625:ℝ),(32114060821765290861703059302514688/10477218233860355671875:ℝ)],
![(3250642318243032095665382556418048/2095443646772071134375:ℝ),(16165829926945014345817421954564096/3492406077953451890625:ℝ),(16078651285842015892265031484571648/3492406077953451890625:ℝ),(15991675667906165117669741372112896/10477218233860355671875:ℝ)]]
theorem admission017_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (119147268443600573522372107/610342199266019794944000000:ℝ) admission017_11_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission017_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_11_coefficients]
def admission017_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28266449504747651072/439453125:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/439453125:ℝ)],
![(56532899009495302144/439453125:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/439453125:ℝ)],
![(28266449504747651072/439453125:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/439453125:ℝ)]]
theorem admission017_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission017_12_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission017_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_12_coefficients]
def admission017_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8952002692921126027264/274658203125:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/274658203125:ℝ)],
![(17904005385842252054528/274658203125:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/274658203125:ℝ)],
![(8952002692921126027264/274658203125:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/274658203125:ℝ)]]
theorem admission017_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission017_13_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission017_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_13_coefficients]
def admission017_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)],
![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)],
![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)]]
theorem admission017_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission017_14_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission017_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_14_coefficients]
theorem admission017_all {δ p : ℝ}
 (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission017_00_pos hd hp
 · exact admission017_01_pos hd hp
 · exact admission017_02_pos hd hp
 · exact admission017_03_pos hd hp
 · exact admission017_04_pos hd hp
 · exact admission017_05_pos hd hp
 · exact admission017_06_pos hd hp
 · exact admission017_07_pos hd hp
 · exact admission017_08_pos hd hp
 · exact admission017_09_pos hd hp
 · exact admission017_10_pos hd hp
 · exact admission017_11_pos hd hp
 · exact admission017_12_pos hd hp
 · exact admission017_13_pos hd hp
 · exact admission017_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission017_all
