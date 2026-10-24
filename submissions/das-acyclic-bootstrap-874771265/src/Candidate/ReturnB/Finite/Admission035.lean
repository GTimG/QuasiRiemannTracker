/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission035_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29172813909110954072735744/15250731:ℝ),(8137604634456511901151002624/1418317983:ℝ),(8135994188271067616008732672/1418317983:ℝ),(2711461247361874443622154240/1418317983:ℝ)],
![(58345627818221908145471488/15250731:ℝ),(16275209268913023802302005248/1418317983:ℝ),(16271988376542135232017465344/1418317983:ℝ),(5422922494723748887244308480/1418317983:ℝ)],
![(29172813909110954072735744/15250731:ℝ),(8137604634456511901151002624/1418317983:ℝ),(8135994188271067616008732672/1418317983:ℝ),(2711461247361874443622154240/1418317983:ℝ)]]
theorem admission035_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission035_00_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission035_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_00_coefficients]
def admission035_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64051686357350907675410432/45752193:ℝ),(5955906111308160314613170176/1418317983:ℝ),(5955005391382686215413170176/1418317983:ℝ),(220522395239156004304191488/157590887:ℝ)],
![(128103372714701815350820864/45752193:ℝ),(11911812222616320629226340352/1418317983:ℝ),(11910010782765372430826340352/1418317983:ℝ),(441044790478312008608382976/157590887:ℝ)],
![(64051686357350907675410432/45752193:ℝ),(5955906111308160314613170176/1418317983:ℝ),(5955005391382686215413170176/1418317983:ℝ),(220522395239156004304191488/157590887:ℝ)]]
theorem admission035_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission035_01_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission035_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_01_coefficients]
def admission035_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(509090372193754346767513550848/714878015625:ℝ),(3155908731271460099818287792128/1477414565625:ℝ),(15777285774708216248389957844992/7387072828125:ℝ),(15775027893059131997688476729344/22161218484375:ℝ)],
![(1018180744387508693535027101696/714878015625:ℝ),(6311817462542920199636575584256/1477414565625:ℝ),(31554571549416432496779915689984/7387072828125:ℝ),(31550055786118263995376953458688/22161218484375:ℝ)],
![(509090372193754346767513550848/714878015625:ℝ),(3155908731271460099818287792128/1477414565625:ℝ),(15777285774708216248389957844992/7387072828125:ℝ),(15775027893059131997688476729344/22161218484375:ℝ)]]
theorem admission035_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission035_02_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission035_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_02_coefficients]
def admission035_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1473229766256088960955580416/1418317983:ℝ),(13255303780769377868482347008/4254953949:ℝ),(13251539967586230953964470272/4254953949:ℝ),(4415925485585119968348864512/4254953949:ℝ)],
![(2945829940524018524351365120/1418317983:ℝ),(26504941338319683199650758656/4254953949:ℝ),(26497413816748547366539231232/4254953949:ℝ),(8829962300000919739942567936/4254953949:ℝ)],
![(1472600174267929563395784704/1418317983:ℝ),(13249637557550305331168411648/4254953949:ℝ),(13245873849162316412574760960/4254953949:ℝ),(4414036814415799771593703424/4254953949:ℝ)]]
theorem admission035_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1960226121163/3872953638912:ℝ) admission035_03_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission035_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_03_coefficients]
def admission035_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1206677764763059588302097088512/7387072828125:ℝ),(723667727840008510446677000192/1477414565625:ℝ),(3616644236751649937509603868672/7387072828125:ℝ),(1204983362314666973578315956224/7387072828125:ℝ)],
![(2414319037767061136876619431936/7387072828125:ℝ),(2413189042024444940731561279488/2462357609375:ℝ),(2412059214742636201628888203264/2462357609375:ℝ),(2410929555921634919568600203264/7387072828125:ℝ)],
![(1207641273004001548574522343424/7387072828125:ℝ),(3621228486873292269961298837504/7387072828125:ℝ),(723906681495251733475412148224/1477414565625:ℝ),(80396412907131196399352283136/492471521875:ℝ)]]
theorem admission035_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (1643888975624577561/20655752740864000000:ℝ) admission035_04_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission035_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_04_coefficients]
def admission035_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(68838905607210469319056031744/714878015625:ℝ),(1280440591022281714488751161344/4432243696875:ℝ),(6402387324360396760687925264384/22161218484375:ℝ),(711396814357504245711635480576/7387072828125:ℝ)],
![(4262663262957957069304933384192/22161218484375:ℝ),(12788361423544493892356101111808/22161218484375:ℝ),(12788732329285841061495936385024/22161218484375:ℝ),(473670463188811582049418739712/2462357609375:ℝ)],
![(2128657189134432520414196400128/22161218484375:ℝ),(6386158468433085319912345305088/22161218484375:ℝ),(1277269000985088860161602224128/4432243696875:ℝ),(141922915041786100087324147712/1477414565625:ℝ)]]
theorem admission035_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (507511422427757387260007/10829563293002104832000000:ℝ) admission035_05_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission035_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_05_coefficients]
def admission035_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(91083279643212770624578005426591172132864/387657074652833159859375:ℝ),(18202440286680791943068664464942176403456/25843804976855543990625:ℝ),(272823436388430947217102604514887410384896/387657074652833159859375:ℝ),(6058007448377179479941599984489729097728/25843804976855543990625:ℝ)],
![(182233668800569431466730681119030085943296/387657074652833159859375:ℝ),(36418298897869513256069138856090709000192/25843804976855543990625:ℝ),(14752651188850233112126054977511402504192/10477218233860355671875:ℝ),(12120485287228983859398275443039422906368/25843804976855543990625:ℝ)],
![(91150389157356660842152675692438913810432/387657074652833159859375:ℝ),(18215858611188721313000474391148532596736/25843804976855543990625:ℝ),(273024657599027677931561429653034482270208/387657074652833159859375:ℝ),(32770150480280023672738786262430777344/139696243118138075625:ℝ)]]
theorem admission035_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (2754862838799990404341588139/24088172131032247907123200000:ℝ) admission035_06_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission035_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_06_coefficients]
def admission035_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1741785507687001386159411433735340425216/3492406077953451890625:ℝ),(3134145808437516496609850630183482032128/2095443646772071134375:ℝ),(15665389180503616601094550041328879665152/10477218233860355671875:ℝ),(1044003332275407655304706238323498156032/2095443646772071134375:ℝ)],
![(3481871843517644850733800044133214060544/3492406077953451890625:ℝ),(6265233629041134536676989143235282599936/2095443646772071134375:ℝ),(31315491029050628441470743334030019657728/10477218233860355671875:ℝ),(2086987682879578062057439550050649767936/2095443646772071134375:ℝ)],
![(1740086335830643464574388610397873635328/3492406077953451890625:ℝ),(3131087820603618040067138513051800567808/2095443646772071134375:ℝ),(15650101848547011840376193292701139992576/10477218233860355671875:ℝ),(1042984350604170406752733311727151611904/2095443646772071134375:ℝ)]]
theorem admission035_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (59286796306660699358004269/244136879706407917977600000:ℝ) admission035_07_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission035_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_07_coefficients]
def admission035_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(99699253256379331044257058235991633956552832/20463316863008507171630859375:ℝ),(6662611957012680743664465248143878116997248/454740374733522381591796875:ℝ),(300537273241028766086739071838242928130702976/20463316863008507171630859375:ℝ),(100418988375981189311053929258124573122379648/20463316863008507171630859375:ℝ)],
![(201405615802390845172663422423313145395935232/20463316863008507171630859375:ℝ),(67294895386076803626319916171013609800451328/2273701873667611907958984375:ℝ),(607091183894867726081593815511860407483858176/20463316863008507171630859375:ℝ),(202842741110832474176430484565158209375731456/20463316863008507171630859375:ℝ)],
![(4068254501840460565136254567492860457575296/818532674520340286865234375:ℝ),(11327278533671133302665863310098073071821696/757900624555870635986328125:ℝ),(12262156426153558399794189746944699174126208/818532674520340286865234375:ℝ),(102423752734851284865376555307033636253351808/20463316863008507171630859375:ℝ)]]
theorem admission035_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (778900416065463523783258267468684640285569/327674973152033777921638268928000000000000000:ℝ) admission035_08_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission035_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_08_coefficients]
def admission035_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(578379539465578477303968699838011629015296/32741306980813611474609375:ℝ),(1732924134923248896871104845700232804696064/32741306980813611474609375:ℝ),(576903318909036813333208221172488508276736/10913768993604537158203125:ℝ),(115233072268774439503743787789692738469888/6548261396162722294921875:ℝ)],
![(1153233384239217998986966094849792216271104/32741306980813611474609375:ℝ),(3455275049346472928459151140387436082364416/32741306980813611474609375:ℝ),(1150283518531182611908487287621541422956544/10913768993604537158203125:ℝ),(229761778127037399522389739767046040715264/6548261396162722294921875:ℝ)],
![(574853844773639521682997395011780587255808/32741306980813611474609375:ℝ),(1722350914423224031588046294687203277668352/32741306980813611474609375:ℝ),(573380199622145798575279066449052914679808/10913768993604537158203125:ℝ),(114528705858262960018645951977353302245376/6548261396162722294921875:ℝ)]]
theorem admission035_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (52081625589500145005625177863/6103421992660197949440000000000:ℝ) admission035_09_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission035_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_09_coefficients]
def admission035_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64619431028574017708405223944768/13850761552734375:ℝ),(107529613753375472303823087350336/7694867529296875:ℝ),(966241736003526987036997318934528/69253807763671875:ℝ),(35730263044829004744019794722816/7694867529296875:ℝ)],
![(643986650154226752232402378574848/69253807763671875:ℝ),(642970680075232656672508313506816/23084602587890625:ℝ),(213984937473896093547104518012928/7694867529296875:ℝ),(640939047268509978513818100170752/69253807763671875:ℝ)],
![(106962836819305656553477880737792/23084602587890625:ℝ),(320380854605561211380047263674368/23084602587890625:ℝ),(191923949932875173304159715721216/13850761552734375:ℝ),(319365696343082344541090429796352/69253807763671875:ℝ)]]
theorem admission035_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (74358120640526140234687/33049204385382400000000000:ℝ) admission035_10_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission035_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_10_coefficients]
def admission035_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4286433910896903549290122041926047760384/10477218233860355671875:ℝ),(4284977955923127683078940648136902705152/3492406077953451890625:ℝ),(4283522213436637379483810598212681596928/3492406077953451890625:ℝ),(4282066683437432638504731892153384435712/10477218233860355671875:ℝ)],
![(8568582499743478082437934937973822849024/10477218233860355671875:ℝ),(8565671334446123144373467467933444734976/3492406077953451890625:ℝ),(342510423760454000185163327646283595776/139696243118138075625:ℝ),(8559850278439158663204782107644758327296/10477218233860355671875:ℝ)],
![(856429717769314906629562579209555017728/2095443646772071134375:ℝ),(4280693378522995461294526819796542029824/3492406077953451890625:ℝ),(4279238380574712625145272592944408297472/3492406077953451890625:ℝ),(4277783595001726024700050215491373891584/10477218233860355671875:ℝ)]]
theorem admission035_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (243163844686576227599064749/1220684398532039589888000000:ℝ) admission035_11_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission035_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_11_coefficients]
def admission035_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7409880138972568242618368/439453125:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/439453125:ℝ)],
![(14819760277945136485236736/439453125:ℝ),(14819760277945136485236736/146484375:ℝ),(14819760277945136485236736/146484375:ℝ),(14819760277945136485236736/439453125:ℝ)],
![(7409880138972568242618368/439453125:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/439453125:ℝ)]]
theorem admission035_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission035_12_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission035_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_12_coefficients]
def admission035_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2346713793933115661291094016/274658203125:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/274658203125:ℝ)],
![(4693427587866231322582188032/274658203125:ℝ),(4693427587866231322582188032/91552734375:ℝ),(4693427587866231322582188032/91552734375:ℝ),(4693427587866231322582188032/274658203125:ℝ)],
![(2346713793933115661291094016/274658203125:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/274658203125:ℝ)]]
theorem admission035_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission035_13_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission035_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_13_coefficients]
def admission035_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)],
![(18446744073709551616/9:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/9:ℝ)],
![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)]]
theorem admission035_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission035_14_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission035_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_14_coefficients]
theorem admission035_all {δ p : ℝ}
 (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission035_00_pos hd hp
 · exact admission035_01_pos hd hp
 · exact admission035_02_pos hd hp
 · exact admission035_03_pos hd hp
 · exact admission035_04_pos hd hp
 · exact admission035_05_pos hd hp
 · exact admission035_06_pos hd hp
 · exact admission035_07_pos hd hp
 · exact admission035_08_pos hd hp
 · exact admission035_09_pos hd hp
 · exact admission035_10_pos hd hp
 · exact admission035_11_pos hd hp
 · exact admission035_12_pos hd hp
 · exact admission035_13_pos hd hp
 · exact admission035_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission035_all
