/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission011_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)],
![(1740282940120050434048/472772661:ℝ),(15613399543800049696768/1418317983:ℝ),(15564252626519645487104/1418317983:ℝ),(5171701903079747092480/1418317983:ℝ)],
![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)]]
theorem admission011_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission011_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission011_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_00_coefficients]
def admission011_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)],
![(3813005592269877673984/1418317983:ℝ),(11411528986115233021952/1418317983:ℝ),(11384041195420833021952/1418317983:ℝ),(420613089063941963776/157590887:ℝ)],
![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)]]
theorem admission011_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission011_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission011_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_01_coefficients]
def admission011_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)],
![(30295193123274185240477696/22161218484375:ℝ),(6045257608730250556997632/1477414565625:ℝ),(30157382964028320329498624/7387072828125:ℝ),(30088477884405387874009088/22161218484375:ℝ)],
![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)]]
theorem admission011_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission011_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission011_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_02_coefficients]
def admission011_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1439182740580804329472/1418317983:ℝ),(12895010279964928901120/4254953949:ℝ),(12837448561019418836992/4254953949:ℝ),(4259986502796902924288/4254953949:ℝ)],
![(2868750822038791258112/1418317983:ℝ),(25703513298352671293440/4254953949:ℝ),(25588415002849021263872/4254953949:ℝ),(8491154170612723744768/4254953949:ℝ)],
![(1429568081457986928640/1418317983:ℝ),(12808503018387742392320/4254953949:ℝ),(12750966441829602426880/4254953949:ℝ),(4231167667815820820480/4254953949:ℝ)]]
theorem admission011_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (985145491505/1936476819456:ℝ) admission011_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission011_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_03_coefficients]
def admission011_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1156764854776694095077376/7387072828125:ℝ),(137789009572825622437888/295482913125:ℝ),(3419216633127547474804736/7387072828125:ℝ),(1131256248583601008934912/7387072828125:ℝ)],
![(2328386989445338158362624/7387072828125:ℝ),(2311285427913049212899328/2462357609375:ℝ),(14801448238823669497856/15886178125:ℝ),(14691639591994818297856/47658534375:ℝ)],
![(1171622134668644063285248/7387072828125:ℝ),(3489131044418507077750784/7387072828125:ℝ),(3463456797925458841698304/7387072828125:ℝ),(381982629391865275744256/2462357609375:ℝ)]]
theorem admission011_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (50571095135074899/645492273152000000:ℝ) admission011_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission011_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_04_coefficients]
def admission011_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2172369396945864677144576/22161218484375:ℝ),(6518801411297943761446912/22161218484375:ℝ),(6520407055062207577032704/22161218484375:ℝ),(241552782301125388081152/2462357609375:ℝ)],
![(4262624714922253379854336/22161218484375:ℝ),(12791790799655731157123072/22161218484375:ℝ),(12795531732472685632098304/22161218484375:ℝ),(1422121882579735951609856/7387072828125:ℝ)],
![(418051063595277740541952/4432243696875:ℝ),(1254597877671557479135232/4432243696875:ℝ),(251004987096419122202624/886448739375:ℝ),(27898541427054391494656/295482913125:ℝ)]]
theorem admission011_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (204126495896131709249/4230298161328947200000:ℝ) admission011_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission011_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_05_coefficients]
def admission011_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(88649360679531592157606740268326912/387657074652833159859375:ℝ),(17513069296747927257126119467343872/25843804976855543990625:ℝ),(259460178407595510243983630771683328/387657074652833159859375:ℝ),(5694231828805917682073238601990144/25843804976855543990625:ℝ)],
![(178335077666858246794954118811471872/387657074652833159859375:ℝ),(7046505505888938397164661893984256/5168760995371108798125:ℝ),(522003025869998824727854609258774528/387657074652833159859375:ℝ),(2291335280578229192931454480285696/5168760995371108798125:ℝ)],
![(17937143397465330927469475708628992/77531414930566631971875:ℝ),(17719458232696764728697190002577408/25843804976855543990625:ℝ),(10501713898496132579354839139483648/15506282986113326394375:ℝ),(5762444574085228282584033799438336/25843804976855543990625:ℝ)]]
theorem admission011_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (84850666356174911291498521/752755379094757747097600000:ℝ) admission011_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission011_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_06_coefficients]
def admission011_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1730857400909126097039908176437248/3492406077953451890625:ℝ),(3098872910334768231819196796002304/2095443646772071134375:ℝ),(15411178017695382193842840682889216/10477218233860355671875:ℝ),(1021877133749783865173316246437888/2095443646772071134375:ℝ)],
![(3435588185788670039594937868668928/3492406077953451890625:ℝ),(6150845708836488695178622321537024/2095443646772071134375:ℝ),(30588493192414457513604268190334976/10477218233860355671875:ℝ),(2028205841119604831299194037731328/2095443646772071134375:ℝ)],
![(340946156975908788511005938446336/698481215590690378125:ℝ),(610394559700344092671885105106944/419088729354414226875:ℝ),(3035463034943815063952285501489152/2095443646772071134375:ℝ),(201265741473964193225175558258688/419088729354414226875:ℝ)]]
theorem admission011_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (5998186513005620039259659/24413687970640791797760000:ℝ) admission011_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission011_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_07_coefficients]
def admission011_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(51945544779988816447844292385677506816/20463316863008507171630859375:ℝ),(11216344865656371867432034826267889248/1364221124200567144775390625:ℝ),(180638126602398654087404888027314435328/20463316863008507171630859375:ℝ),(64338283608632317105401797155436103424/20463316863008507171630859375:ℝ)],
![(5402241502125161758698488960554538752/818532674520340286865234375:ℝ),(4617292400184930597970354280445872144/220035665193639862060546875:ℝ),(145158217704289057489633352776372736/6548261396162722294921875:ℝ),(159266843689281473113431555262243409408/20463316863008507171630859375:ℝ)],
![(83110492773140227519617931628185961984/20463316863008507171630859375:ℝ),(87054340077450989199920808562482590224/6821105621002835723876953125:ℝ),(272981303723504650567699339398850364672/20463316863008507171630859375:ℝ),(3062211615504811484129992196993784064/660106995580919586181640625:ℝ)]]
theorem admission011_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (202912284296831314249391767131552761/156247603012101067505664000000000000000:ℝ) admission011_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission011_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_08_coefficients]
def admission011_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(676320790417279711931210113527630688/32741306980813611474609375:ℝ),(1992717140753485511549528312673754112/32741306980813611474609375:ℝ),(652184850721104618531513311503843328/10913768993604537158203125:ℝ),(128031697609505067445168833468301312/6548261396162722294921875:ℝ)],
![(1297956230367295459590564177168362288/32741306980813611474609375:ℝ),(3822328349507039332879908001172987392/32741306980813611474609375:ℝ),(1250316542843953702020778245787353088/10913768993604537158203125:ℝ),(245315616738305186692433678100856832/6548261396162722294921875:ℝ)],
![(24865417598000629906374162545629264/1309652279232544458984375:ℝ),(365922241750710764266075937699846656/6548261396162722294921875:ℝ),(119626338424569816697852986856701952/2182753798720907431640625:ℝ),(23456783825760023849452968926511104/1309652279232544458984375:ℝ)]]
theorem admission011_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (5592533070030218088496439201/610342199266019794944000000000:ℝ) admission011_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission011_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_09_coefficients]
def admission011_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(386746539718350075225770128/69253807763671875:ℝ),(75716160259310613255923312/4616920517578125:ℝ),(1111286718819190263171838976/69253807763671875:ℝ),(40254555154226376617639936/7694867529296875:ℝ)],
![(148108787014297523942584112/13850761552734375:ℝ),(144873515518500839026498832/4616920517578125:ℝ),(47214554620094706749021184/1538973505859375:ℝ),(138419289103866117604278272/13850761552734375:ℝ)],
![(152065908013492733128276/29786583984375:ℝ),(148621061787639832136732/9928861328125:ℝ),(1306637235760221338344192/89359751953125:ℝ),(425245588985378548498432/89359751953125:ℝ)]]
theorem admission011_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (25954930968345858673/10661033672704000000000:ℝ) admission011_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission011_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_10_coefficients]
def admission011_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4262099858840303054372112781942784/10477218233860355671875:ℝ),(4239341344778867939115648873095168/3492406077953451890625:ℝ),(4216635773800760993979211339268096/3492406077953451890625:ℝ),(4193983145905982218962800180461568/10477218233860355671875:ℝ)],
![(8458298428282711396513433334943744/10477218233860355671875:ℝ),(8412964019758620882426323757641728/3492406077953451890625:ℝ),(8367735059942878458503116673253376/3492406077953451890625:ℝ),(8322611548835484124743812081778688/10477218233860355671875:ℝ)],
![(839239713888481668428264110600192/2095443646772071134375:ℝ),(834724534995950588662134976909312/698481215590690378125:ℝ),(830219857228423492904781066797056/698481215590690378125:ℝ),(825725680585900381156202380263424/2095443646772071134375:ℝ)]]
theorem admission011_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (24608542936620127593165707/122068439853203958988800000:ℝ) admission011_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission011_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_11_coefficients]
def admission011_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)],
![(14133224752373825536/439453125:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/439453125:ℝ)],
![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)]]
theorem admission011_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission011_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission011_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_12_coefficients]
def admission011_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)],
![(4476001346460563013632/274658203125:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/274658203125:ℝ)],
![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)]]
theorem admission011_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission011_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission011_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_13_coefficients]
def admission011_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission011_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission011_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission011_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_14_coefficients]
theorem admission011_all {δ p : ℝ}
 (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission011_00_pos hd hp
 · exact admission011_01_pos hd hp
 · exact admission011_02_pos hd hp
 · exact admission011_03_pos hd hp
 · exact admission011_04_pos hd hp
 · exact admission011_05_pos hd hp
 · exact admission011_06_pos hd hp
 · exact admission011_07_pos hd hp
 · exact admission011_08_pos hd hp
 · exact admission011_09_pos hd hp
 · exact admission011_10_pos hd hp
 · exact admission011_11_pos hd hp
 · exact admission011_12_pos hd hp
 · exact admission011_13_pos hd hp
 · exact admission011_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission011_all
