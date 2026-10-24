/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission006_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2656247851633344512/45752193:ℝ),(245495209036888408064/1418317983:ℝ),(243959367871875776512/1418317983:ℝ),(80807842235621048320/1418317983:ℝ)],
![(5312495703266689024/45752193:ℝ),(490990418073776816128/1418317983:ℝ),(487918735743751553024/1418317983:ℝ),(161615684471242096640/1418317983:ℝ)],
![(2656247851633344512/45752193:ℝ),(245495209036888408064/1418317983:ℝ),(243959367871875776512/1418317983:ℝ),(80807842235621048320/1418317983:ℝ)]]
theorem admission006_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission006_00_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission006_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_00_coefficients]
def admission006_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1935732551897317376/45752193:ℝ),(179164133867250515968/1418317983:ℝ),(178305140408050515968/1418317983:ℝ),(6572079516624093184/157590887:ℝ)],
![(3871465103794634752/45752193:ℝ),(358328267734501031936/1418317983:ℝ),(356610280816101031936/1418317983:ℝ),(13144159033248186368/157590887:ℝ)],
![(1935732551897317376/45752193:ℝ),(179164133867250515968/1418317983:ℝ),(178305140408050515968/1418317983:ℝ),(6572079516624093184/157590887:ℝ)]]
theorem admission006_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission006_01_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission006_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_01_coefficients]
def admission006_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15373945747047874297856/714878015625:ℝ),(474439034420267463999488/7387072828125:ℝ),(94457150136410164953088/1477414565625:ℝ),(470132466943834185531392/22161218484375:ℝ)],
![(30747891494095748595712/714878015625:ℝ),(948878068840534927998976/7387072828125:ℝ),(188914300272820329906176/1477414565625:ℝ),(940264933887668371062784/22161218484375:ℝ)],
![(15373945747047874297856/714878015625:ℝ),(474439034420267463999488/7387072828125:ℝ),(94457150136410164953088/1477414565625:ℝ),(470132466943834185531392/22161218484375:ℝ)]]
theorem admission006_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission006_02_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission006_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_02_coefficients]
def admission006_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(138080693997057081344/4254953949:ℝ),(410627883771455602688/4254953949:ℝ),(407022650876539961344/4254953949:ℝ),(134475461102141440000/4254953949:ℝ)],
![(8850229902960492544/137256579:ℝ),(815845950387115786240/4254953949:ℝ),(808638568413305765888/4254953949:ℝ),(267149745017965248512/4254953949:ℝ)],
![(136276432994718187520/4254953949:ℝ),(405218066615660183552/4254953949:ℝ),(401615917536765804544/4254953949:ℝ),(132674283915823808512/4254953949:ℝ)]]
theorem admission006_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (494250222727/968238409728:ℝ) admission006_03_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission006_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_03_coefficients]
def admission006_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12156657507276625915904/2462357609375:ℝ),(107825097792110928662528/7387072828125:ℝ),(106247769301268744372224/7387072828125:ℝ),(34892644030987693457408/7387072828125:ℝ)],
![(2383191188400237261824/238292671875:ℝ),(72815429360903224411136/2462357609375:ℝ),(71756958926259127058432/2462357609375:ℝ),(70703515536475063058432/7387072828125:ℝ)],
![(37408954318577477368832/7387072828125:ℝ),(22124238058119748914176/1477414565625:ℝ),(109023107477508636803072/7387072828125:ℝ),(11936957168495789867008/2462357609375:ℝ)]]
theorem admission006_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478581916447053/161373068288000000:ℝ) admission006_04_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission006_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_04_coefficients]
def admission006_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(191309306843174446592/59096582625:ℝ),(215273324648358726721024/22161218484375:ℝ),(215312874181096640155136/22161218484375:ℝ),(71780539598928330906112/22161218484375:ℝ)],
![(3073703917361807101952/492471521875:ℝ),(415117156659414030497792/22161218484375:ℝ),(415262532470923802057728/22161218484375:ℝ),(138462052092791091147776/22161218484375:ℝ)],
![(4438379081006060141056/1477414565625:ℝ),(199843832011055303776768/22161218484375:ℝ),(199949658289827161902592/22161218484375:ℝ),(66681512493862760241664/22161218484375:ℝ)]]
theorem admission006_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (26006127427769883639/528787270166118400000:ℝ) admission006_05_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission006_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_05_coefficients]
def admission006_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(315421790701238243285660005117952/43073008294759239984375:ℝ),(8312780720556026576641028614172672/387657074652833159859375:ℝ),(261651178339113345669434964967424/12505066924284940640625:ℝ),(175813096360206471298826356391936/25843804976855543990625:ℝ)],
![(638132895540366771403081409913856/43073008294759239984375:ℝ),(16820701033316303675638346299442176/387657074652833159859375:ℝ),(16415858342777941897554274799583232/387657074652833159859375:ℝ),(355889489300369855129577412624384/25843804976855543990625:ℝ)],
![(322711104839128528117421404795904/43073008294759239984375:ℝ),(8507920312760277098997317685269504/387657074652833159859375:ℝ),(8304671814265428181801790885593088/387657074652833159859375:ℝ),(180076392940163383830751056232448/25843804976855543990625:ℝ)]]
theorem admission006_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (20958554310823258316376967/188188844773689436774400000:ℝ) admission006_06_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission006_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_06_coefficients]
def admission006_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(168601841250600959047154652614656/10477218233860355671875:ℝ),(500495139538162962903725860655104/10477218233860355671875:ℝ),(495205762868769537254145259470848/10477218233860355671875:ℝ),(6532498583248301335902962057216/419088729354414226875:ℝ)],
![(332264926119838443633853537307648/10477218233860355671875:ℝ),(986254200297877715896117375388672/10477218233860355671875:ℝ),(975755320096715933105087423709184/10477218233860355671875:ℝ),(64353209183735332168564717125632/2095443646772071134375:ℝ)],
![(163663084869237484586698884692992/10477218233860355671875:ℝ),(485759060759714752992391514733568/10477218233860355671875:ℝ),(480549557227946395850942164238336/10477218233860355671875:ℝ),(31690716267493825489049906839552/2095443646772071134375:ℝ)]]
theorem admission006_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (15111311086413300270581201/61034219926601979494400000:ℝ) admission006_07_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission006_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_07_coefficients]
def admission006_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(145722058468376346333539769156853304/6821105621002835723876953125:ℝ),(2161646812920204072884811609050233016/20463316863008507171630859375:ℝ),(3009344819614108311020867764070713352/20463316863008507171630859375:ℝ),(428270394079409651041357810409513416/6821105621002835723876953125:ℝ)],
![(952783132048771115146713758273093476/6821105621002835723876953125:ℝ),(10202637995943913717009228876955942164/20463316863008507171630859375:ℝ),(11825909940863308887835799271201317392/20463316863008507171630859375:ℝ),(1493838214659170112554131473972593552/6821105621002835723876953125:ℝ)],
![(807061073580394768813173989116240172/6821105621002835723876953125:ℝ),(8040991183023709644124417267905709148/20463316863008507171630859375:ℝ),(1763313024249840115362986301426120808/4092663372601701434326171875:ℝ),(1065567820579760461512773663563080136/6821105621002835723876953125:ℝ)]]
theorem admission006_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (18215257308547043291692471144606663/52082534337367022501888000000000000000:ℝ) admission006_08_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission006_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_08_coefficients]
def admission006_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24908037507825703057640369693718176/32741306980813611474609375:ℝ),(72328827623763895334048553237058048/32741306980813611474609375:ℝ),(23314894274340443360386753253146624/10913768993604537158203125:ℝ),(7207668266528124487101240836096/10477218233860355671875:ℝ)],
![(46338629082876817205141725541162488/32741306980813611474609375:ℝ),(134344998870575630459461243812224384/32741306980813611474609375:ℝ),(43231824499119241152337455864922112/10913768993604537158203125:ℝ),(8337849178116096346507551742885888/6548261396162722294921875:ℝ)],
![(21430591575051114147501355847444312/32741306980813611474609375:ℝ),(62016171246811735125412690575166336/32741306980813611474609375:ℝ),(19916930224778797791950702611775488/10913768993604537158203125:ℝ),(3833056511536018542069276220325888/6548261396162722294921875:ℝ)]]
theorem admission006_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (14621950193542551201130967027/1525855498165049487360000000000:ℝ) admission006_09_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission006_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_09_coefficients]
def admission006_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4799603505625719213900896/23084602587890625:ℝ),(41602600029976547107348768/69253807763671875:ℝ),(40014342110250701059689472/69253807763671875:ℝ),(4270195705925437198014464/23084602587890625:ℝ)],
![(26771161131393292935428464/69253807763671875:ℝ),(25727463643758652531124176/23084602587890625:ℝ),(24687338933035827248869888/23084602587890625:ℝ),(946034277956492683546624/2770152310546875:ℝ)],
![(2468264443602015224996522/13850761552734375:ℝ),(35487726001857324676112786/69253807763671875:ℝ),(33956623471491088623708992/69253807763671875:ℝ),(10810255122682902572578816/69253807763671875:ℝ)]]
theorem admission006_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5278444884122511021767/2065575274086400000000000:ℝ) admission006_10_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission006_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_10_coefficients]
def admission006_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(138461180622645936793252654280704/10477218233860355671875:ℝ),(137009218793965693752455518769152/3492406077953451890625:ℝ),(135563984215278534495699244417024/3492406077953451890625:ℝ),(26825095377316891804596766244864/2095443646772071134375:ℝ)],
![(272769207459719460352961700967424/10477218233860355671875:ℝ),(269888220616783501343632274275328/3492406077953451890625:ℝ),(267020578909256647383347005620224/3492406077953451890625:ℝ),(264166282337138898472105895002112/10477218233860355671875:ℝ)],
![(26861605367414704711941809337344/2095443646772071134375:ℝ),(132879001822817807591176755506176/3492406077953451890625:ℝ),(5258263787759124515505910448128/139696243118138075625:ℝ),(130040805450554439449122063777792/10477218233860355671875:ℝ)]]
theorem admission006_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (62008288121487827038346321/305171099633009897472000000:ℝ) admission006_11_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission006_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_11_coefficients]
def admission006_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(220831636755841024/439453125:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/439453125:ℝ)],
![(441663273511682048/439453125:ℝ),(441663273511682048/146484375:ℝ),(441663273511682048/146484375:ℝ),(441663273511682048/439453125:ℝ)],
![(220831636755841024/439453125:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/439453125:ℝ)]]
theorem admission006_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission006_12_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission006_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_12_coefficients]
def admission006_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69937521038446297088/274658203125:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/274658203125:ℝ)],
![(139875042076892594176/274658203125:ℝ),(139875042076892594176/91552734375:ℝ),(139875042076892594176/91552734375:ℝ),(139875042076892594176/274658203125:ℝ)],
![(69937521038446297088/274658203125:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/274658203125:ℝ)]]
theorem admission006_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission006_13_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission006_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_13_coefficients]
def admission006_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(549755813888/9:ℝ),(549755813888/3:ℝ),(549755813888/3:ℝ),(549755813888/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)]]
theorem admission006_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission006_14_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission006_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_14_coefficients]
theorem admission006_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission006_00_pos hd hp
 · exact admission006_01_pos hd hp
 · exact admission006_02_pos hd hp
 · exact admission006_03_pos hd hp
 · exact admission006_04_pos hd hp
 · exact admission006_05_pos hd hp
 · exact admission006_06_pos hd hp
 · exact admission006_07_pos hd hp
 · exact admission006_08_pos hd hp
 · exact admission006_09_pos hd hp
 · exact admission006_10_pos hd hp
 · exact admission006_11_pos hd hp
 · exact admission006_12_pos hd hp
 · exact admission006_13_pos hd hp
 · exact admission006_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission006_all
