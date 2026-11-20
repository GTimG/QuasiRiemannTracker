/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission037_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)],
![(1740282940120050434048/472772661:ℝ),(15613399543800049696768/1418317983:ℝ),(15564252626519645487104/1418317983:ℝ),(5171701903079747092480/1418317983:ℝ)],
![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)]]
theorem admission037_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission037_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission037_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_00_coefficients]
def admission037_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)],
![(3813005592269877673984/1418317983:ℝ),(11411528986115233021952/1418317983:ℝ),(11384041195420833021952/1418317983:ℝ),(420613089063941963776/157590887:ℝ)],
![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)]]
theorem admission037_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission037_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission037_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_01_coefficients]
def admission037_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)],
![(30295193123274185240477696/22161218484375:ℝ),(6045257608730250556997632/1477414565625:ℝ),(30157382964028320329498624/7387072828125:ℝ),(30088477884405387874009088/22161218484375:ℝ)],
![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)]]
theorem admission037_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission037_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission037_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_02_coefficients]
def admission037_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1424748180702893178880/1418317983:ℝ),(12765173252648238841856/4254953949:ℝ),(12707686960864839073792/4254953949:ℝ),(4216758250325279768576/4254953949:ℝ)],
![(2839881702282968956928/1418317983:ℝ),(25443839243719291174912/4254953949:ℝ),(25328891802539861737472/4254953949:ℝ),(8404697665669477433344/4254953949:ℝ)],
![(1415133521580075778048/1418317983:ℝ),(12678665991071052333056/4254953949:ℝ),(12621204841675022663680/4254953949:ℝ),(4187939415344197664768/4254953949:ℝ)]]
theorem admission037_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (487540314829/968238409728:ℝ) admission037_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission037_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_03_coefficients]
def admission037_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1179299235064551772254208/7387072828125:ℝ),(140473211058010537160704/295482913125:ℝ),(3485824749357304893145088/7387072828125:ℝ),(1153293707971593236381696/7387072828125:ℝ)],
![(2373455750021053512716288/7387072828125:ℝ),(2356022119332797791612928/2462357609375:ℝ),(2338629887837507051061248/2462357609375:ℝ),(2321279055535181291061248/7387072828125:ℝ)],
![(238831302991300348092416/1477414565625:ℝ),(114717292953165482123264/238292671875:ℝ),(3530064914155216260038656/7387072828125:ℝ),(389328449187862684893184/2462357609375:ℝ)]]
theorem admission037_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (103112492678009859/1290984546304000000:ℝ) admission037_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission037_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_04_coefficients]
def admission037_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2049198278491650715492352/22161218484375:ℝ),(6150878697840116549091328/22161218484375:ℝ),(6154073277469660896088064/22161218484375:ℝ),(228043650902355006943232/2462357609375:ℝ)],
![(910928210028084703232/5026359375:ℝ),(12055945372740076732411904/22161218484375:ℝ),(12062864177287592270209024/22161218484375:ℝ),(1341067094187113664782336/7387072828125:ℝ)],
![(1967084199522174741057536/22161218484375:ℝ),(5905066674899960183320576/22161218484375:ℝ),(1181758179963586274824192/4432243696875:ℝ),(131387228296009728790528/1477414565625:ℝ)]]
theorem admission037_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (480245165898968442641/10575745403322368000000:ℝ) admission037_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission037_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_05_coefficients]
def admission037_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2438476833354926786090155760816128/10477218233860355671875:ℝ),(17825278750837541969540752684527616/25843804976855543990625:ℝ),(264103825265665457429166998090153984/387657074652833159859375:ℝ),(5796550946724883582839431398162432/25843804976855543990625:ℝ)],
![(36296728395211928930082432915042304/77531414930566631971875:ℝ),(35856946437623921410652575904288768/25843804976855543990625:ℝ),(106258063917227743819644268779143168/77531414930566631971875:ℝ),(11661314638729077766189657993773056/25843804976855543990625:ℝ)],
![(91259999141927353565076401425014784/387657074652833159859375:ℝ),(18031667686786379441111823219761152/25843804976855543990625:ℝ),(7221256603256034099163630967717888/10477218233860355671875:ℝ),(5864763692004194183350226595610624/25843804976855543990625:ℝ)]]
theorem admission037_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (172750680050995456660969001/1505510758189515494195200000:ℝ) admission037_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission037_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_06_coefficients]
def admission037_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1691348618770286881203868861681664/3492406077953451890625:ℝ),(3028140493545457972153356032749568/2095443646772071134375:ℝ),(15059429082315626800165966397308928/10477218233860355671875:ℝ),(998554494179839516602158563721216/2095443646772071134375:ℝ)],
![(671314124302198321584571847831552/698481215590690378125:ℝ),(6009380875257868175846940795031552/2095443646772071134375:ℝ),(1195399812866197869050020784766976/419088729354414226875:ℝ),(63921308450958584972802537816064/67594956347486165625:ℝ)],
![(1665222002740704726718990377476096/3492406077953451890625:ℝ),(2981240381712410203693584762281984/2095443646772071134375:ℝ),(14825566239339319926084553221865472/10477218233860355671875:ℝ),(983006067799876617554720108576768/2095443646772071134375:ℝ)]]
theorem admission037_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (14647931870816299580852987/61034219926601979494400000:ℝ) admission037_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission037_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_07_coefficients]
def admission037_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(98692966769715933055504751249440189568/20463316863008507171630859375:ℝ),(20450429917212426463556323712201239088/1364221124200567144775390625:ℝ),(10239528774081783667913124695181747584/660106995580919586181640625:ℝ),(109361691034955717205625221145787028352/20463316863008507171630859375:ℝ)],
![(228550881532583277182783141741388834304/20463316863008507171630859375:ℝ),(235476914921293394498323871553155534864/6821105621002835723876953125:ℝ),(727193961114176583890908182472804279552/20463316863008507171630859375:ℝ),(249313658541928273313878403242945259264/20463316863008507171630859375:ℝ)],
![(129857914762867344127278390491948644736/20463316863008507171630859375:ℝ),(133224765335231262180542252992149339424/6821105621002835723876953125:ℝ),(409768569117641290185601316922170104448/20463316863008507171630859375:ℝ),(139951967506972556108253182097158230912/20463316863008507171630859375:ℝ)]]
theorem admission037_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (771038802888405726996130869136251481/312495206024202135011328000000000000000:ℝ) admission037_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission037_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_08_coefficients]
def admission037_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(592873077620774930599921880135026864/32741306980813611474609375:ℝ),(1745224360569551775344922188954471936/32741306980813611474609375:ℝ),(570633713531625124889048096110936064/10913768993604537158203125:ℝ),(111910029888447645148312850214682624/6548261396162722294921875:ℝ)],
![(226212160954857179385597542076630928/6548261396162722294921875:ℝ),(665468557827834372094139150746884608/6548261396162722294921875:ℝ),(217442853692998942947169563000307712/2182753798720907431640625:ℝ),(213072281296190342098721711593619456/6548261396162722294921875:ℝ)],
![(17360894424306805365421478395100896/1056171192929471337890625:ℝ),(1582118428569620085125773564779951104/32741306980813611474609375:ℝ),(516580554933369589846799718890602496/10913768993604537158203125:ℝ),(101162251407742696950408861378936832/6548261396162722294921875:ℝ)]]
theorem admission037_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (12059480119674527281571490929/1525855498165049487360000000000:ℝ) admission037_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission037_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_09_coefficients]
def admission037_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(336230877019112485301527204/69253807763671875:ℝ),(328542660929853043751413132/23084602587890625:ℝ),(192519891491128290260551936/13850761552734375:ℝ),(104400833000494622616682496/23084602587890625:ℝ)],
![(127609530868482160016196464/13850761552734375:ℝ),(622834451020973035266233104/23084602587890625:ℝ),(607644715650588053354533888/23084602587890625:ℝ),(592478744740474604345884672/69253807763671875:ℝ)],
![(100524206033843791605182128/23084602587890625:ℝ),(98016327483810490793281424/7694867529296875:ℝ),(171922061625044541088695296/13850761552734375:ℝ),(279036128071365913119490048/69253807763671875:ℝ)]]
theorem admission037_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4257753419057707414543/2065575274086400000000000:ℝ) admission037_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission037_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_10_coefficients]
def admission037_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4162428105111339387452418513833984/10477218233860355671875:ℝ),(4140217449846243421473409326166016/3492406077953451890625:ℝ),(823611685057910175077195148427264/698481215590690378125:ℝ),(4095951031441261749190117761744896/10477218233860355671875:ℝ)],
![(8258954920824784062674044798726144/10477218233860355671875:ℝ),(8214716229893371847141844663783424/3492406077953451890625:ℝ),(8170580362920458221316645478989824/3492406077953451890625:ℝ),(262146687738904618877369265946624/337974781737430828125:ℝ)],
![(819305363142688935044325256978432/2095443646772071134375:ℝ),(4074498780047128425668435337617408/3492406077953451890625:ℝ),(4052521937630907345930669736853504/3492406077953451890625:ℝ),(4030596288464781436008329482600448/10477218233860355671875:ℝ)]]
theorem admission037_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (60060565001737794816618107/305171099633009897472000000:ℝ) admission037_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission037_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_11_coefficients]
def admission037_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)],
![(14133224752373825536/439453125:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/439453125:ℝ)],
![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)]]
theorem admission037_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission037_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission037_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_12_coefficients]
def admission037_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)],
![(4476001346460563013632/274658203125:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/274658203125:ℝ)],
![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)]]
theorem admission037_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission037_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission037_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_13_coefficients]
def admission037_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission037_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission037_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission037_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_14_coefficients]
theorem admission037_all {δ p : ℝ}
 (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission037_00_pos hd hp
 · exact admission037_01_pos hd hp
 · exact admission037_02_pos hd hp
 · exact admission037_03_pos hd hp
 · exact admission037_04_pos hd hp
 · exact admission037_05_pos hd hp
 · exact admission037_06_pos hd hp
 · exact admission037_07_pos hd hp
 · exact admission037_08_pos hd hp
 · exact admission037_09_pos hd hp
 · exact admission037_10_pos hd hp
 · exact admission037_11_pos hd hp
 · exact admission037_12_pos hd hp
 · exact admission037_13_pos hd hp
 · exact admission037_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission037_all
