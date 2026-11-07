/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission024_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)],
![(1740282940120050434048/472772661:ℝ),(15613399543800049696768/1418317983:ℝ),(15564252626519645487104/1418317983:ℝ),(5171701903079747092480/1418317983:ℝ)],
![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)]]
theorem admission024_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission024_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission024_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_00_coefficients]
def admission024_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)],
![(3813005592269877673984/1418317983:ℝ),(11411528986115233021952/1418317983:ℝ),(11384041195420833021952/1418317983:ℝ),(420613089063941963776/157590887:ℝ)],
![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)]]
theorem admission024_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission024_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission024_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_01_coefficients]
def admission024_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)],
![(30295193123274185240477696/22161218484375:ℝ),(6045257608730250556997632/1477414565625:ℝ),(30157382964028320329498624/7387072828125:ℝ),(30088477884405387874009088/22161218484375:ℝ)],
![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)]]
theorem admission024_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission024_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission024_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_02_coefficients]
def admission024_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1429559700662196895744/1418317983:ℝ),(12808452261753802194944/4254953949:ℝ),(12750940827583032328192/4254953949:ℝ),(4231167667815820820480/4254953949:ℝ)],
![(2849504742201576390656/1418317983:ℝ),(25530397261930417881088/4254953949:ℝ),(25415399535976248246272/4254953949:ℝ),(8433516500650559537152/4254953949:ℝ)],
![(1419945041539379494912/1418317983:ℝ),(12721945000176615686144/4254953949:ℝ),(12664458708393215918080/4254953949:ℝ),(4202348832834738716672/4254953949:ℝ)]]
theorem admission024_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (978435583607/1936476819456:ℝ) admission024_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission024_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_03_coefficients]
def admission024_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(390595924989533071065088/2462357609375:ℝ),(46526159076538521862144/98494304375:ℝ),(1154540681315795251232768/2462357609375:ℝ),(381982629391865275744256/2462357609375:ℝ)],
![(31445771064388645261312/98494304375:ℝ),(226559021502536928907264/238292671875:ℝ),(6971484252692682874290176/7387072828125:ℝ),(2306587415943186472763392/7387072828125:ℝ)],
![(395548351620183060467712/2462357609375:ℝ),(3533867735838255656464384/7387072828125:ℝ),(3507862208745297120591872/7387072828125:ℝ),(1160639527767590645530624/7387072828125:ℝ)]]
theorem admission024_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25613931302180793/322746136576000000:ℝ) admission024_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission024_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_04_coefficients]
def admission024_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(418051063595277740541952/4432243696875:ℝ),(6273519602326058953209856/22161218484375:ℝ),(6276184536667176456402944/22161218484375:ℝ),(697640084105835401967616/7387072828125:ℝ)],
![(4098396556983301430984704/22161218484375:ℝ),(2460245436342392308129792/4432243696875:ℝ),(12307086695682623390838784/22161218484375:ℝ),(1368085356984654427058176/7387072828125:ℝ)],
![(455464105014042351616/5026359375:ℝ),(6027707579385902587439104/22161218484375:ℝ),(1206180431803089386887168/4432243696875:ℝ),(44696351525254601672704/492471521875:ℝ)]]
theorem admission024_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (222394582526387867/4797344251904000000:ℝ) admission024_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission024_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_05_coefficients]
def admission024_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(89698882115932058109426088856240128/387657074652833159859375:ℝ),(478951592778585686452320944472064/698481215590690378125:ℝ),(262555942979642141700772542317330432/387657074652833159859375:ℝ),(5762444574085228282584033799438336/25843804976855543990625:ℝ)],
![(180434120539659178698592815987298304/387657074652833159859375:ℝ),(35648806801564178269042820426166272/25843804976855543990625:ℝ),(17038534032712647988433304269357056/12505066924284940640625:ℝ),(11593101893449767165678862796324864/25843804976855543990625:ℝ)],
![(90735238423727120589166727131058176/387657074652833159859375:ℝ),(17927597868756507870306945480699904/25843804976855543990625:ℝ),(265638612034449945940659890032738304/387657074652833159859375:ℝ),(5830657319364538883094828996886528/25843804976855543990625:ℝ)]]
theorem admission024_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (42933557734528394658744587/376377689547378873548800000:ℝ) admission024_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission024_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_06_coefficients]
def admission024_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1704518212816566619815881966600192/3492406077953451890625:ℝ),(610343593161712278408393924100096/419088729354414226875:ℝ),(15176678727442211931391591159169024/10477218233860355671875:ℝ),(201265741473964193225175558258688/419088729354414226875:ℝ)],
![(3382909809603551085146885448994816/3492406077953451890625:ℝ),(6056535819784075015624167970533376/2095443646772071134375:ℝ),(30119494611908116988701769142894592/10477218233860355671875:ℝ),(1997108988359679033204317127442432/2095443646772071134375:ℝ)],
![(54141664412483369849387209109504/112658260579143609375:ℝ),(96929608192758503986522527420416/67594956347486165625:ℝ),(482026318853738872816457354313728/337974781737430828125:ℝ),(31960654225479292486401268908032/67594956347486165625:ℝ)]]
theorem admission024_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (952501720949390306663551/3937691608167869644800000:ℝ) admission024_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission024_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_07_coefficients]
def admission024_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83110492773140227519617931628185961984/20463316863008507171630859375:ℝ),(17372401566693741598181560750223455808/1364221124200567144775390625:ℝ),(271829636865156413832672873042860928512/20463316863008507171630859375:ℝ),(94353888559514583838884079815670053376/20463316863008507171630859375:ℝ)],
![(197385933539431866111009502498880379136/20463316863008507171630859375:ℝ),(204696631416106545844576241933377702064/6821105621002835723876953125:ℝ),(636002450851418824145640197457257786368/20463316863008507171630859375:ℝ),(219298053591046006580396120582711309312/20463316863008507171630859375:ℝ)],
![(114275440766291638591391570870694417152/20463316863008507171630859375:ℝ),(117834623582637837853668438182260423024/6821105621002835723876953125:ℝ),(364172813986262410312967324414396857856/20463316863008507171630859375:ℝ),(124944165031531422741512040767041255936/20463316863008507171630859375:ℝ)]]
theorem admission024_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (162325181197539506874253772711300707/78123801506050533752832000000000000000:ℝ) admission024_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission024_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_08_coefficients]
def admission024_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(620688981886276524377017957932561472/32741306980813611474609375:ℝ),(1827721953964196354079790896860899328/32741306980813611474609375:ℝ),(597817425928118289436536501241905152/10913768993604537158203125:ℝ),(23456783825760023849452968926511104/1309652279232544458984375:ℝ)],
![(1186692613305289084482179865978223856/32741306980813611474609375:ℝ),(3492337975928461017940433169547277824/32741306980813611474609375:ℝ),(1141581693257981043830824625263476736/10913768993604537158203125:ℝ),(223820059776895290296625700429365248/6548261396162722294921875:ℝ)],
![(566003631419012560105161908045662384/32741306980813611474609375:ℝ),(1664616021964264663860642272686378496/32741306980813611474609375:ℝ),(543764267329862754394288124021571584/10913768993604537158203125:ℝ),(106536140648095171049360855796809728/6548261396162722294921875:ℝ)]]
theorem admission024_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (25400195276283066522922719907/3051710996330098974720000000000:ℝ) admission024_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission024_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_09_coefficients]
def admission024_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(70663526405620147698882368/13850761552734375:ℝ),(345467538663838599487751872/23084602587890625:ℝ),(112543365294342584270163968/7694867529296875:ℝ),(329805449131293198462631936/69253807763671875:ℝ)],
![(672709482803921186394569056/69253807763671875:ℝ),(21199026508655522097060064/744664599609375:ℝ),(1924964570080447780955764736/69253807763671875:ℝ),(41744325355689527488249856/4616920517578125:ℝ)],
![(106382563851351169312082828/23084602587890625:ℝ),(103819825154931355462044804/7694867529296875:ℝ),(182269980212092903841384704/13850761552734375:ℝ),(296119313536424890484768768/69253807763671875:ℝ)]]
theorem admission024_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (18073688570338433257127/8262301096345600000000000:ℝ) admission024_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission024_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_10_coefficients]
def admission024_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4195652023020993943092316603203584/10477218233860355671875:ℝ),(166930349926284730427499567005696/139696243118138075625:ℝ),(4150917541459954248250387607846912/3492406077953451890625:ℝ),(825725680585900381156202380263424/2095443646772071134375:ℝ)],
![(8325402756644093173953840977465344/10477218233860355671875:ℝ),(8280798826515121525570004361736192/3492406077953451890625:ℝ),(8236298595261264967045469210411008/3492406077953451890625:ℝ),(8191902062882523498380235523489792/10477218233860355671875:ℝ)],
![(26643553120149027295880802414592/67594956347486165625:ℝ),(132501292850258169834919844728832/112658260579143609375:ℝ),(131786485606493894154680051695616/112658260579143609375:ℝ),(131073343869452309438684632973312/337974781737430828125:ℝ)]]
theorem admission024_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (3906290050430664701422591/19688458040839348224000000:ℝ) admission024_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission024_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_11_coefficients]
def admission024_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)],
![(14133224752373825536/439453125:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/439453125:ℝ)],
![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)]]
theorem admission024_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission024_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission024_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_12_coefficients]
def admission024_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)],
![(4476001346460563013632/274658203125:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/274658203125:ℝ)],
![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)]]
theorem admission024_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission024_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission024_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_13_coefficients]
def admission024_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission024_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission024_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission024_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_14_coefficients]
theorem admission024_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission024_00_pos hd hp
 · exact admission024_01_pos hd hp
 · exact admission024_02_pos hd hp
 · exact admission024_03_pos hd hp
 · exact admission024_04_pos hd hp
 · exact admission024_05_pos hd hp
 · exact admission024_06_pos hd hp
 · exact admission024_07_pos hd hp
 · exact admission024_08_pos hd hp
 · exact admission024_09_pos hd hp
 · exact admission024_10_pos hd hp
 · exact admission024_11_pos hd hp
 · exact admission024_12_pos hd hp
 · exact admission024_13_pos hd hp
 · exact admission024_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission024_all
