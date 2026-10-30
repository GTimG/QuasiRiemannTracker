/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission014_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2656247851633344512/45752193:ℝ),(245495209036888408064/1418317983:ℝ),(243959367871875776512/1418317983:ℝ),(80807842235621048320/1418317983:ℝ)],
![(5312495703266689024/45752193:ℝ),(490990418073776816128/1418317983:ℝ),(487918735743751553024/1418317983:ℝ),(161615684471242096640/1418317983:ℝ)],
![(2656247851633344512/45752193:ℝ),(245495209036888408064/1418317983:ℝ),(243959367871875776512/1418317983:ℝ),(80807842235621048320/1418317983:ℝ)]]
theorem admission014_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission014_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission014_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_00_coefficients]
def admission014_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1935732551897317376/45752193:ℝ),(179164133867250515968/1418317983:ℝ),(178305140408050515968/1418317983:ℝ),(6572079516624093184/157590887:ℝ)],
![(3871465103794634752/45752193:ℝ),(358328267734501031936/1418317983:ℝ),(356610280816101031936/1418317983:ℝ),(13144159033248186368/157590887:ℝ)],
![(1935732551897317376/45752193:ℝ),(179164133867250515968/1418317983:ℝ),(178305140408050515968/1418317983:ℝ),(6572079516624093184/157590887:ℝ)]]
theorem admission014_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission014_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission014_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_01_coefficients]
def admission014_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15373945747047874297856/714878015625:ℝ),(474439034420267463999488/7387072828125:ℝ),(94457150136410164953088/1477414565625:ℝ),(470132466943834185531392/22161218484375:ℝ)],
![(30747891494095748595712/714878015625:ℝ),(948878068840534927998976/7387072828125:ℝ),(188914300272820329906176/1477414565625:ℝ),(940264933887668371062784/22161218484375:ℝ)],
![(15373945747047874297856/714878015625:ℝ),(474439034420267463999488/7387072828125:ℝ),(94457150136410164953088/1477414565625:ℝ),(470132466943834185531392/22161218484375:ℝ)]]
theorem admission014_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission014_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission014_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_02_coefficients]
def admission014_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(136273349178696925184/4254953949:ℝ),(405211781018817658880/4254953949:ℝ),(401612715755944542208/4254953949:ℝ),(132674283915823808512/4254953949:ℝ)],
![(270742437355054956544/4254953949:ℝ),(805013744881839898624/4254953949:ℝ),(797818698172114927616/4254953949:ℝ),(263547390645329985536/4254953949:ℝ)],
![(134469088176358031360/4254953949:ℝ),(399801963863022239744/4254953949:ℝ),(396205982416170385408/4254953949:ℝ),(130873106729506177024/4254953949:ℝ)]]
theorem admission014_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (487540314829/968238409728:ℝ) admission014_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission014_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_03_coefficients]
def admission014_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12476569546941800282112/2462357609375:ℝ),(36887533455195844016128/2462357609375:ℝ),(36347921076749833601024/2462357609375:ℝ),(11936957168495789867008/2462357609375:ℝ)],
![(75798399078398401313792/7387072828125:ℝ),(44824258645932576001024/1477414565625:ℝ),(220862864636738894036992/7387072828125:ℝ),(72539970485474415345664/7387072828125:ℝ)],
![(38368690437573000467456/7387072828125:ℝ),(113458692864075347956736/7387072828125:ℝ),(22363820281297878646784/1477414565625:ℝ),(7345819795997409148928/1477414565625:ℝ)]]
theorem admission014_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25613931302180793/322746136576000000:ℝ) admission014_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission014_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_04_coefficients]
def admission014_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4438379081006060141056/1477414565625:ℝ),(199910250927050426900992/22161218484375:ℝ),(200082353951856229718528/22161218484375:ℝ),(66747789239896704933376/22161218484375:ℝ)],
![(8532404571938819258368/1477414565625:ℝ),(384391009216797430857728/22161218484375:ℝ),(384801492012442981184512/22161218484375:ℝ),(128396551374727839202304/22161218484375:ℝ)],
![(1364675163644253039104/492471521875:ℝ),(184480758289747003956736/22161218484375:ℝ),(184719138060586751465984/22161218484375:ℝ),(61648762134831134268928/22161218484375:ℝ)]]
theorem admission014_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (23988430610934135453/528787270166118400000:ℝ) admission014_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission014_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_05_coefficients]
def admission014_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(322894924677090625395974971406336/43073008294759239984375:ℝ),(8511211558866466557416995263543296/387657074652833159859375:ℝ),(8306308753920281583914486364372992/387657074652833159859375:ℝ),(180076392940163383830751056232448/25843804976855543990625:ℝ)],
![(653079163492071535623711342490624/43073008294759239984375:ℝ),(17217562709937183637190279598183424/387657074652833159859375:ℝ),(16806102793593477633878279700348928/387657074652833159859375:ℝ),(364416082460283680193426812305408/25843804976855543990625:ℝ)],
![(330184238814980910227736371084288/43073008294759239984375:ℝ),(8706351151070717079773284334640128/387657074652833159859375:ℝ),(8499794039673196049963793335975936/387657074652833159859375:ℝ),(36867937904024059272535151214592/5168760995371108798125:ℝ)]]
theorem admission014_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (42933557734528394658744587/376377689547378873548800000:ℝ) admission014_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission014_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_06_coefficients]
def admission014_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(163583211731612416078567634003968/10477218233860355671875:ℝ),(485599631712481760938030720509952/10477218233860355671875:ℝ),(480470001318338472304712620703744/10477218233860355671875:ℝ),(31690716267493825489049906839552/2095443646772071134375:ℝ)],
![(322227667081861357696679500086272/10477218233860355671875:ℝ),(956463184646515311964727095098368/10477218233860355671875:ℝ),(946283796995853803206222146174976/10477218233860355671875:ℝ),(62409655886239969787634910232576/2095443646772071134375:ℝ)],
![(158644455350248941618111866082304/10477218233860355671875:ℝ),(470863552934033551026696374588416/10477218233860355671875:ℝ),(465813795677515330901509525471232/10477218233860355671875:ℝ),(30718939618746144298585003393024/2095443646772071134375:ℝ)]]
theorem admission014_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (14647931870816299580852987/61034219926601979494400000:ℝ) admission014_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission014_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_07_coefficients]
def admission014_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(807061073580394768813173989116240172/6821105621002835723876953125:ℝ),(7968284417119049413047314947126703468/20463316863008507171630859375:ℝ),(8671734286876127040292287270556012916/20463316863008507171630859375:ℝ),(1041526231968092849504555296757259988/6821105621002835723876953125:ℝ)],
![(2275461162272807960105982198191867212/6821105621002835723876953125:ℝ),(21815913204341604397334235553108883068/20463316863008507171630859375:ℝ),(4630137775077469269275727656834383304/4092663372601701434326171875:ℝ),(2720349890436536509480526446668086696/6821105621002835723876953125:ℝ)],
![(293680017738482638258561641815125408/1364221124200567144775390625:ℝ),(553905151488902199371476824239287184/818532674520340286865234375:ℝ),(14478954588511219306086351013615903604/20463316863008507171630859375:ℝ),(1678823658468443659975971149910826708/6821105621002835723876953125:ℝ)]]
theorem admission014_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (201765268395098692203293497279060043/104165068674734045003776000000000000000:ℝ) admission014_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission014_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_08_coefficients]
def admission014_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21311826417496821549207338512341008/32741306980813611474609375:ℝ),(61779557195520463852311817446786304/32741306980813611474609375:ℝ),(19877646950437448535359648481574912/10913768993604537158203125:ℝ),(3833056511536018542069276220325888/6548261396162722294921875:ℝ)],
![(39146206902219054188275663178408152/32741306980813611474609375:ℝ),(113246458014088767495987772231680896/32741306980813611474609375:ℝ),(36357329851313251502283246321778688/10913768993604537158203125:ℝ),(6994376868027977821769553138417664/6548261396162722294921875:ℝ)],
![(17834380484722232639068324666067144/32741306980813611474609375:ℝ),(51466900818568303643675954784894592/32741306980813611474609375:ℝ),(16479682900875802966923597840203776/10913768993604537158203125:ℝ),(3161320356491959279700276918091776/6548261396162722294921875:ℝ)]]
theorem admission014_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (12059480119674527281571490929/1525855498165049487360000000000:ℝ) admission014_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission014_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_09_coefficients]
def admission014_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12312153246583594058370952/69253807763671875:ℝ),(3939983392912453776426568/7694867529296875:ℝ),(3776436751039805047121152/7694867529296875:ℝ),(10840269831136005494622208/69253807763671875:ℝ)],
![(7491244334927309697930776/23084602587890625:ℝ),(12905726469195737622941864/13850761552734375:ℝ),(61644989227859802222566656/69253807763671875:ℝ),(6530054513939764400549888/23084602587890625:ℝ)],
![(2026110272338455173335642/13850761552734375:ℝ),(28976716910324518316959234/69253807763671875:ℝ),(27566007251135864735265088/69253807763671875:ℝ),(8719879002230184784984064/69253807763671875:ℝ)]]
theorem admission014_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4257753419057707414543/2065575274086400000000000:ℝ) admission014_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission014_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_10_coefficients]
def admission014_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(134239544487531129900027206539264/10477218233860355671875:ℝ),(132833456287699941003759759689728/3492406077953451890625:ℝ),(131433876608707710853458045435904/3492406077953451890625:ℝ),(130040805450554439449122063777792/10477218233860355671875:ℝ)],
![(264325935189489846566510805484544/10477218233860355671875:ℝ),(52307339120850399169248151223296/698481215590690378125:ℝ),(258760363696115000098864607657984/3492406077953451890625:ℝ),(255996939465078859324382360109056/10477218233860355671875:ℝ)],
![(26017278140391743333296719789056/2095443646772071134375:ℝ),(128703239316552054842480996426752/3492406077953451890625:ℝ),(25465297417481457849081312444416/698481215590690378125:ℝ),(125956134014524419875260296331264/10477218233860355671875:ℝ)]]
theorem admission014_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (60060565001737794816618107/305171099633009897472000000:ℝ) admission014_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission014_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_11_coefficients]
def admission014_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(220831636755841024/439453125:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/439453125:ℝ)],
![(441663273511682048/439453125:ℝ),(441663273511682048/146484375:ℝ),(441663273511682048/146484375:ℝ),(441663273511682048/439453125:ℝ)],
![(220831636755841024/439453125:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/439453125:ℝ)]]
theorem admission014_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission014_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission014_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_12_coefficients]
def admission014_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69937521038446297088/274658203125:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/274658203125:ℝ)],
![(139875042076892594176/274658203125:ℝ),(139875042076892594176/91552734375:ℝ),(139875042076892594176/91552734375:ℝ),(139875042076892594176/274658203125:ℝ)],
![(69937521038446297088/274658203125:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/274658203125:ℝ)]]
theorem admission014_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission014_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission014_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_13_coefficients]
def admission014_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(549755813888/9:ℝ),(549755813888/3:ℝ),(549755813888/3:ℝ),(549755813888/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)]]
theorem admission014_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission014_14_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission014_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_14_coefficients]
theorem admission014_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission014_00_pos hd hp
 · exact admission014_01_pos hd hp
 · exact admission014_02_pos hd hp
 · exact admission014_03_pos hd hp
 · exact admission014_04_pos hd hp
 · exact admission014_05_pos hd hp
 · exact admission014_06_pos hd hp
 · exact admission014_07_pos hd hp
 · exact admission014_08_pos hd hp
 · exact admission014_09_pos hd hp
 · exact admission014_10_pos hd hp
 · exact admission014_11_pos hd hp
 · exact admission014_12_pos hd hp
 · exact admission014_13_pos hd hp
 · exact admission014_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission014_all
