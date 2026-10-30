/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission027_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(294911353309858027798528/157590887:ℝ),(7956315733954275011723264/1418317983:ℝ),(7950024928542383272886272/1418317983:ℝ),(2647911374376830511349760/1418317983:ℝ)],
![(589822706619716055597056/157590887:ℝ),(15912631467908550023446528/1418317983:ℝ),(15900049857084766545772544/1418317983:ℝ),(5295822748753661022699520/1418317983:ℝ)],
![(294911353309858027798528/157590887:ℝ),(7956315733954275011723264/1418317983:ℝ),(7950024928542383272886272/1418317983:ℝ),(2647911374376830511349760/1418317983:ℝ)]]
theorem admission027_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission027_00_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission027_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_00_coefficients]
def admission027_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1941703551615527769079808/1418317983:ℝ),(5821592217637700107239424/1418317983:ℝ),(5818073780428816907239424/1418317983:ℝ),(215353901600738285453312/157590887:ℝ)],
![(3883407103231055538159616/1418317983:ℝ),(11643184435275400214478848/1418317983:ℝ),(11636147560857633814478848/1418317983:ℝ),(430707803201476570906624/157590887:ℝ)],
![(1941703551615527769079808/1418317983:ℝ),(5821592217637700107239424/1418317983:ℝ),(5818073780428816907239424/1418317983:ℝ),(215353901600738285453312/157590887:ℝ)]]
theorem admission027_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission027_01_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission027_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_01_coefficients]
def admission027_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3086352045478152930880126976/4432243696875:ℝ),(15422940377199029300097974272/7387072828125:ℝ),(15414120527007293945795313664/7387072828125:ℝ),(15405300676815558591492653056/22161218484375:ℝ)],
![(6172704090956305861760253952/4432243696875:ℝ),(30845880754398058600195948544/7387072828125:ℝ),(30828241054014587891590627328/7387072828125:ℝ),(30810601353631117182985306112/22161218484375:ℝ)],
![(3086352045478152930880126976/4432243696875:ℝ),(15422940377199029300097974272/7387072828125:ℝ),(15414120527007293945795313664/7387072828125:ℝ),(15405300676815558591492653056/22161218484375:ℝ)]]
theorem admission027_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission027_02_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission027_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_02_coefficients]
def admission027_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(160469170762667106762752/157590887:ℝ),(12983290950925110248210432/4254953949:ℝ),(12968583788666184848637952/4254953949:ℝ),(4317960448333086483021824/4254953949:ℝ)],
![(961995107518537051144192/472772661:ℝ),(25944445765510935668064256/4254953949:ℝ),(25915033072755118155235328/4254953949:ℝ),(8628543274911015947468800/4254953949:ℝ)],
![(480587595230535730855936/472772661:ℝ),(12961154814585825419853824/4254953949:ℝ),(12946449284088933306597376/4254953949:ℝ),(4310582826577929464446976/4254953949:ℝ)]]
theorem admission027_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1960226121163/3872953638912:ℝ) admission027_03_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission027_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_03_coefficients]
def admission027_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1891111921627110916685824/11819316525:ℝ),(1132549480516221353787392/2363863305:ℝ),(5652165348729332594376704/11819316525:ℝ),(1880529867775336742125568/11819316525:ℝ)],
![(2367661543823291093516091392/7387072828125:ℝ),(2363246196744096859388837888/2462357609375:ℝ),(2358833480287907028597211136/2462357609375:ℝ),(2354423394454721601141211136/7387072828125:ℝ)],
![(1185716592806346770587451392/7387072828125:ℝ),(3550521463619098847580913664/7387072828125:ℝ),(3543897097907888214306193408/7387072828125:ℝ),(393030742365045379104243712/2462357609375:ℝ)]]
theorem admission027_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656767469286687/8262301096345600:ℝ) admission027_04_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission027_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_04_coefficients]
def admission027_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2099410888511793886711513088/22161218484375:ℝ),(6298937412428272784354443264/22161218484375:ℝ),(6299636472522716771273867264/22161218484375:ℝ),(700036649535412624543645696/7387072828125:ℝ)],
![(33423218335995299393896448/177289747875:ℝ),(12535150248884723808315047936/22161218484375:ℝ),(12536582239075438553898287104/22161218484375:ℝ),(1393111427396709056606765056/7387072828125:ℝ)],
![(2078491403487618537525542912/22161218484375:ℝ),(6236212836456451023960604672/22161218484375:ℝ),(1247389153310544356524883968/4432243696875:ℝ),(46204985190753095470874624/492471521875:ℝ)]]
theorem admission027_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (31715261894037148094567/676847705812631552000000:ℝ) admission027_05_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission027_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_05_coefficients]
def admission027_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17894991374141688412036178740890632192/77531414930566631971875:ℝ),(5946466417565720820289672602894270464/8614601658951847996875:ℝ),(53351629881817198344465171872852475904/77531414930566631971875:ℝ),(1181894895051805103646286479179644928/5168760995371108798125:ℝ)],
![(179212689908444419240626975395968385024/387657074652833159859375:ℝ),(640345837209335814477403499939168256/463150626825368171875:ℝ),(534302947756892926504417779488263241728/387657074652833159859375:ℝ),(11836411413309554550193628362343186432/25843804976855543990625:ℝ)],
![(89737733037735977180446081691515224064/387657074652833159859375:ℝ),(29819830772639626644950162479871295488/43073008294759239984375:ℝ),(8630477366058288218777158713677447168/12505066924284940640625:ℝ),(5926936938050529031962195966444961792/25843804976855543990625:ℝ)]]
theorem admission027_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (137590674573067238513180809/1204408606551612395356160000:ℝ) admission027_06_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission027_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_06_coefficients]
def admission027_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(38025897823842402674806270508990464/77609023954521153125:ℝ),(3075916202383931099752431460621942784/2095443646772071134375:ℝ),(614347352636068378506654505225945088/419088729354414226875:ℝ),(1022519802040155665000610369250525184/2095443646772071134375:ℝ)],
![(1138561074860309317475971175477215232/1164135359317817296875:ℝ),(30699374580986221854193250176627441664/10477218233860355671875:ℝ),(30657620941878642136134892067252862976/10477218233860355671875:ℝ),(408211841385408165569015298796814336/419088729354414226875:ℝ)],
![(568172607502673277353877117842358272/1164135359317817296875:ℝ),(15319793569066566355431092873517727744/10477218233860355671875:ℝ),(15298937125976932673468529436604235776/10477218233860355671875:ℝ),(1018539404886885162844466124733546496/2095443646772071134375:ℝ)]]
theorem admission027_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (59286796306660699358004269/244136879706407917977600000:ℝ) admission027_07_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission027_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_07_coefficients]
def admission027_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18671516737265848317551708626063029574624/4092663372601701434326171875:ℝ),(18860861215112258546535938998423165172512/1364221124200567144775390625:ℝ),(57150478320466636053119276472177228885088/4092663372601701434326171875:ℝ),(19239410715029119200484054918348887942176/4092663372601701434326171875:ℝ)],
![(7783317822677552478785519347569794643328/818532674520340286865234375:ℝ),(196464155482955108232511408956016544936512/6821105621002835723876953125:ℝ),(19194669218977382048833719842501303258176/660106995580919586181640625:ℝ),(1291775599529854856541376175400257466304/132021399116183917236328125:ℝ)],
![(20245072376121914076375888111785943642016/4092663372601701434326171875:ℝ),(102159849407393815499831713963900719073952/6821105621002835723876953125:ℝ),(309282354185965663248248932756654256578016/20463316863008507171630859375:ℝ),(20805632870396381352298606519059093513248/4092663372601701434326171875:ℝ)]]
theorem admission027_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (583484898039557759923490894564469674207/255996072775026389001279897600000000000000:ℝ) admission027_08_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission027_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_08_coefficients]
def admission027_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(116335472054050873670414558241714377408/6548261396162722294921875:ℝ),(13890634124185661408522136646514630656/261930455846508891796875:ℝ),(115175416909024660359848303314553798656/2182753798720907431640625:ℝ),(114595870605770388631872358619835006976/6548261396162722294921875:ℝ)],
![(229907433289289646150599479203280634944/6548261396162722294921875:ℝ),(3431266324939796162887387635117198352384/32741306980813611474609375:ℝ),(1137976899598481499085791307721120677888/10913768993604537158203125:ℝ),(9057612396819212421003251843908763648/261930455846508891796875:ℝ)],
![(113571961235238772480184920961566257536/6548261396162722294921875:ℝ),(1694937059416588486822120554302869520384/32741306980813611474609375:ℝ),(562099815053358197286549791148351684608/10913768993604537158203125:ℝ),(111844439314709921893208937477884084224/6548261396162722294921875:ℝ)]]
theorem admission027_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (52081625589500145005625177863/6103421992660197949440000000000:ℝ) admission027_09_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission027_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_09_coefficients]
def admission027_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(326469946866017714489636027152/69253807763671875:ℝ),(324475438864450740226673727152/23084602587890625:ℝ),(967445213409339429865040531456/69253807763671875:ℝ),(106829615338866550079051792384/23084602587890625:ℝ)],
![(644316231208223452738080775744/69253807763671875:ℝ),(640337473856340827408978256064/23084602587890625:ℝ),(636360320688835954754334736384/23084602587890625:ℝ),(632384776382368991024150216704/69253807763671875:ℝ)],
![(105943617434954268125082798784/23084602587890625:ℝ),(10188600789494504497989587264/744664599609375:ℝ),(941589581611096059778691842048/69253807763671875:ℝ),(311880562835041352090908622848/69253807763671875:ℝ)]]
theorem admission027_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (74358120640526140234687/33049204385382400000000000:ℝ) admission027_10_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission027_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_10_coefficients]
def admission027_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4211346995698273937292793880147984384/10477218233860355671875:ℝ),(4205645957167463353708706731799281664/3492406077953451890625:ℝ),(4199948243999989385001335634425544704/3492406077953451890625:ℝ),(4194253856195852031170680588026773504/10477218233860355671875:ℝ)],
![(8405928261217594780882879345074307072/10477218233860355671875:ℝ),(8394537829814297923558646991077834752/3492406077953451890625:ℝ),(8383154042138341363986628334917255168/3492406077953451890625:ℝ),(1674355379637945020433364675318513664/2095443646772071134375:ℝ)],
![(4194581265519320843590085464926322688/10477218233860355671875:ℝ),(4188891872646834569849940259278553088/3492406077953451890625:ℝ),(4183205798138351978985292700491710464/3492406077953451890625:ℝ),(4177523041993873070996142788565794816/10477218233860355671875:ℝ)]]
theorem admission027_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (243163844686576227599064749/1220684398532039589888000000:ℝ) admission027_11_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission027_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_11_coefficients]
def admission027_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7236211073215398674432/439453125:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/439453125:ℝ)],
![(14472422146430797348864/439453125:ℝ),(14472422146430797348864/146484375:ℝ),(14472422146430797348864/146484375:ℝ),(14472422146430797348864/439453125:ℝ)],
![(7236211073215398674432/439453125:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/146484375:ℝ),(7236211073215398674432/439453125:ℝ)]]
theorem admission027_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission027_12_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission027_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_12_coefficients]
def admission027_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2291712689387808262979584/274658203125:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/274658203125:ℝ)],
![(4583425378775616525959168/274658203125:ℝ),(4583425378775616525959168/91552734375:ℝ),(4583425378775616525959168/91552734375:ℝ),(4583425378775616525959168/274658203125:ℝ)],
![(2291712689387808262979584/274658203125:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/91552734375:ℝ),(2291712689387808262979584/274658203125:ℝ)]]
theorem admission027_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission027_13_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission027_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_13_coefficients]
def admission027_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)],
![(18014398509481984/9:ℝ),(18014398509481984/3:ℝ),(18014398509481984/3:ℝ),(18014398509481984/9:ℝ)],
![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)]]
theorem admission027_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission027_14_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission027_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_14_coefficients]
theorem admission027_all {δ p : ℝ}
 (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission027_00_pos hd hp
 · exact admission027_01_pos hd hp
 · exact admission027_02_pos hd hp
 · exact admission027_03_pos hd hp
 · exact admission027_04_pos hd hp
 · exact admission027_05_pos hd hp
 · exact admission027_06_pos hd hp
 · exact admission027_07_pos hd hp
 · exact admission027_08_pos hd hp
 · exact admission027_09_pos hd hp
 · exact admission027_10_pos hd hp
 · exact admission027_11_pos hd hp
 · exact admission027_12_pos hd hp
 · exact admission027_13_pos hd hp
 · exact admission027_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission027_all
