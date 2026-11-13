/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission030_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29172813909110954072735744/15250731:ℝ),(8137604634456511901151002624/1418317983:ℝ),(8135994188271067616008732672/1418317983:ℝ),(2711461247361874443622154240/1418317983:ℝ)],
![(58345627818221908145471488/15250731:ℝ),(16275209268913023802302005248/1418317983:ℝ),(16271988376542135232017465344/1418317983:ℝ),(5422922494723748887244308480/1418317983:ℝ)],
![(29172813909110954072735744/15250731:ℝ),(8137604634456511901151002624/1418317983:ℝ),(8135994188271067616008732672/1418317983:ℝ),(2711461247361874443622154240/1418317983:ℝ)]]
theorem admission030_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission030_00_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission030_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_00_coefficients]
def admission030_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64051686357350907675410432/45752193:ℝ),(5955906111308160314613170176/1418317983:ℝ),(5955005391382686215413170176/1418317983:ℝ),(220522395239156004304191488/157590887:ℝ)],
![(128103372714701815350820864/45752193:ℝ),(11911812222616320629226340352/1418317983:ℝ),(11910010782765372430826340352/1418317983:ℝ),(441044790478312008608382976/157590887:ℝ)],
![(64051686357350907675410432/45752193:ℝ),(5955906111308160314613170176/1418317983:ℝ),(5955005391382686215413170176/1418317983:ℝ),(220522395239156004304191488/157590887:ℝ)]]
theorem admission030_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission030_01_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission030_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_01_coefficients]
def admission030_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(509090372193754346767513550848/714878015625:ℝ),(3155908731271460099818287792128/1477414565625:ℝ),(15777285774708216248389957844992/7387072828125:ℝ),(15775027893059131997688476729344/22161218484375:ℝ)],
![(1018180744387508693535027101696/714878015625:ℝ),(6311817462542920199636575584256/1477414565625:ℝ),(31554571549416432496779915689984/7387072828125:ℝ),(31550055786118263995376953458688/22161218484375:ℝ)],
![(509090372193754346767513550848/714878015625:ℝ),(3155908731271460099818287792128/1477414565625:ℝ),(15777285774708216248389957844992/7387072828125:ℝ),(15775027893059131997688476729344/22161218484375:ℝ)]]
theorem admission030_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission030_02_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission030_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_02_coefficients]
def admission030_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1473544579716028325722849280/1418317983:ℝ),(13258136997234470110663540736/4254953949:ℝ),(13254373079256165200221437952/4254953949:ℝ),(4416869821169780066726445056/4254953949:ℝ)],
![(2946459567443897253885902848/1418317983:ℝ),(26510607771249867684013146112/4254953949:ℝ),(26503080040088415859053166592/4254953949:ℝ),(8831850971170239936697729024/4254953949:ℝ)],
![(1472914987727868928163053568/1418317983:ℝ),(13252470774015397573349605376/4254953949:ℝ),(13248706960832250658831728640/4254953949:ℝ),(4414981150000459869971283968/4254953949:ℝ)]]
theorem admission030_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (15685163923253/30983629111296:ℝ) admission030_03_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission030_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_03_coefficients]
def admission030_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(402065224056089371411885326336/2462357609375:ℝ),(241126202564349619541561573376/492471521875:ℝ),(1205066437655164222086699810816/2462357609375:ℝ),(401500648889505495790777270272/2462357609375:ℝ)],
![(804451617525826062914579070976/2462357609375:ℝ),(7236675924603738303974761037824/7387072828125:ℝ),(7233287796655594062387655737344/7387072828125:ℝ),(2409966724629333947156631912448/7387072828125:ℝ)],
![(80477278693947338300538748928/492471521875:ℝ),(3619782886138494010851337437184/7387072828125:ℝ),(3618088483690101396127556304896/7387072828125:ℝ),(1205464777960817459784300101632/7387072828125:ℝ)]]
theorem admission030_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (821616104077645437/10327876370432000000:ℝ) admission030_04_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission030_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_04_coefficients]
def admission030_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2136680516168070563129007276032/22161218484375:ℝ),(6410224114756093782260355432448/22161218484375:ℝ),(6410406316761711177853028532224/22161218484375:ℝ),(237429190908187550969075597312/2462357609375:ℝ)],
![(137677811214420938638112063488/714878015625:ℝ),(12804403742833864311989300363264/22161218484375:ℝ),(12804770314088469895826142920704/22161218484375:ℝ),(1422792906300551560539438841856/7387072828125:ℝ)],
![(2131331631478978534652466692096/22161218484375:ℝ),(6394179628077770529728944930816/22161218484375:ℝ),(1278872799465351743594622877696/4432243696875:ℝ),(142101066715197781526442409984/1477414565625:ℝ)]]
theorem admission030_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (4065192473371464795403417/86636506344016838656000000:ℝ) admission030_05_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission030_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_05_coefficients]
def admission030_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(91049698057628567153366401216193165787136/387657074652833159859375:ℝ),(18195727547884799922409467749825767276544/25843804976855543990625:ℝ),(272722798963513276741732977543089544495104/387657074652833159859375:ℝ),(6055772253139867030184062247459746742272/25843804976855543990625:ℝ)],
![(36433301125880204904861494539646814650368/77531414930566631971875:ℝ),(36404873420277529214750745425857890746368/25843804976855543990625:ℝ),(109129363827524656839584956044865232175104/77531414930566631971875:ℝ),(12116014896754358959883199968979458195456/25843804976855543990625:ℝ)],
![(91116807571772457370941071482040907464704/387657074652833159859375:ℝ),(18209145872392729292341277676032123469824/25843804976855543990625:ℝ),(272924020174110007456191802681236616380416/387657074652833159859375:ℝ),(6060242643614491929699137721519711453184/25843804976855543990625:ℝ)]]
theorem admission030_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1376923194843554263157798743/12044086065516123953561600000:ℝ) admission030_06_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission030_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_06_coefficients]
def admission030_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1742635528150661600617790151575851761664/3492406077953451890625:ℝ),(3135675323764559080324603357420643680256/2095443646772071134375:ℝ),(15673034149925941997673109840484020256768/10477218233860355671875:ℝ),(1044512823111026279580692701621671428096/2095443646772071134375:ℝ)],
![(696714376888993055930111495962847346688/698481215590690378125:ℝ),(6268292659695219704106494597709605896192/2095443646772071134375:ℝ),(6266156193579055846925572586468060168192/2095443646772071134375:ℝ),(2088006664550815310609412476646996312064/2095443646772071134375:ℝ)],
![(1740936356294303679032767328238384971776/3492406077953451890625:ℝ),(3132617335930660623781891240288962215936/2095443646772071134375:ℝ),(15657746817969337236954753091856280584192/10477218233860355671875:ℝ),(1043493841439789031028719775025324883968/2095443646772071134375:ℝ)]]
theorem admission030_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (474526060061084095208898259/1953095037651263343820800000:ℝ) admission030_07_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission030_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_07_coefficients]
def admission030_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(98695698611563239502182405260326695215138048/20463316863008507171630859375:ℝ),(6595760436810420941867722708606574973662464/454740374733522381591796875:ℝ),(297531299762666846804847358929863193132495104/20463316863008507171630859375:ℝ),(99417778661927185298805956184880448732822272/20463316863008507171630859375:ℝ)],
![(199398506512758662088514116471983267913105664/20463316863008507171630859375:ℝ),(22208793394684735202784163591880192789034496/757900624555870635986328125:ℝ),(601079236938143887517810389695100937487442432/20463316863008507171630859375:ℝ),(6478720054281434391997888336086127761181184/660106995580919586181640625:ℝ)],
![(100702807901195422586331711211656572697967616/20463316863008507171630859375:ℝ),(33647578000002100899013877232607703498791168/2273701873667611907958984375:ℝ),(9791868941144420668160097766620572398546688/660106995580919586181640625:ℝ),(101422543020797280853128582233789511863794432/20463316863008507171630859375:ℝ)]]
theorem admission030_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (385530072701418904305400020548151153184133/163837486576016888960819134464000000000000000:ℝ) admission030_08_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission030_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_08_coefficients]
def admission030_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(580144318131238734212195415133394080213504/32741306980813611474609375:ℝ),(1738214607344437666015929628120716560039936/32741306980813611474609375:ℝ),(578665522169649129378392786365075511312384/10913768993604537158203125:ℝ),(115585255474030179246292705695862456582144/6548261396162722294921875:ℝ)],
![(231352588314107702560683905088111423733504/6548261396162722294921875:ℝ),(693171198837770093349760141045680718610432/6548261396162722294921875:ℝ),(230761585010481448799771283601343085805568/2182753798720907431640625:ℝ),(230466144537548879007487575579385476939776/6548261396162722294921875:ℝ)],
![(576618623439299778591224110307163038454016/32741306980813611474609375:ℝ),(1727641386844412800732871077107687033012224/32741306980813611474609375:ℝ),(575142402882758114620463631641639917715456/10913768993604537158203125:ℝ),(114880889063518699761194869883523020357632/6548261396162722294921875:ℝ)]]
theorem admission030_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (417934239752935172004781160953/48827375941281583595520000000000:ℝ) admission030_09_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission030_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_09_coefficients]
def admission030_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10458080490024337751167403309824/2233993798828125:ℝ),(323691523965412216603363823510272/23084602587890625:ℝ),(2585460833487429556235399856128/184676820703125:ℝ),(322673735889717209220622978121728/69253807763671875:ℝ)],
![(129239059871374980756122875522304/13850761552734375:ℝ),(215059337968298104272760337329408/7694867529296875:ℝ),(1932482493567907011758785445494784/69253807763671875:ℝ),(71460416809439499346200754126848/7694867529296875:ℝ)],
![(107331273204226913154827419456448/23084602587890625:ℝ),(321485505729937067833925400696512/23084602587890625:ℝ),(192586345882591787960873146974208/13850761552734375:ℝ),(320469031873271693618634291150848/69253807763671875:ℝ)]]
theorem admission030_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4775360701579923832694207/2115149080664473600000000000:ℝ) admission030_10_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission030_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_10_coefficients]
def admission030_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4288577688729379258530090349473315160064/10477218233860355671875:ℝ),(4287120989105406597961013638146258108416/3492406077953451890625:ℝ),(857132900416141765384001553029989924864/698481215590690378125:ℝ),(4284208227655285945407072730484389707776/10477218233860355671875:ℝ)],
![(8572870055408429500917871553068357648384/10477218233860355671875:ℝ),(8569957400810680974137613447952155541504/3492406077953451890625:ℝ),(8567045171299492899501477525031625949184/3492406077953451890625:ℝ),(8564133366874865277009463784306768871424/10477218233860355671875:ℝ)],
![(856858473335810048477556240719008497664/2095443646772071134375:ℝ),(4282836411705274376176599809805897433088/3492406077953451890625:ℝ),(4281380669218784072581469759881676324864/3492406077953451890625:ℝ),(4279925139219579331602391053822379163648/10477218233860355671875:ℝ)]]
theorem admission030_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1946284619052484836903382099/9765475188256316719104000000:ℝ) admission030_11_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission030_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_11_coefficients]
def admission030_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7409880138972568242618368/439453125:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/439453125:ℝ)],
![(14819760277945136485236736/439453125:ℝ),(14819760277945136485236736/146484375:ℝ),(14819760277945136485236736/146484375:ℝ),(14819760277945136485236736/439453125:ℝ)],
![(7409880138972568242618368/439453125:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/146484375:ℝ),(7409880138972568242618368/439453125:ℝ)]]
theorem admission030_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission030_12_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission030_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_12_coefficients]
def admission030_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2346713793933115661291094016/274658203125:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/274658203125:ℝ)],
![(4693427587866231322582188032/274658203125:ℝ),(4693427587866231322582188032/91552734375:ℝ),(4693427587866231322582188032/91552734375:ℝ),(4693427587866231322582188032/274658203125:ℝ)],
![(2346713793933115661291094016/274658203125:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/91552734375:ℝ),(2346713793933115661291094016/274658203125:ℝ)]]
theorem admission030_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission030_13_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission030_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_13_coefficients]
def admission030_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)],
![(18446744073709551616/9:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/9:ℝ)],
![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)]]
theorem admission030_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission030_14_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission030_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_14_coefficients]
theorem admission030_all {δ p : ℝ}
 (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission030_00_pos hd hp
 · exact admission030_01_pos hd hp
 · exact admission030_02_pos hd hp
 · exact admission030_03_pos hd hp
 · exact admission030_04_pos hd hp
 · exact admission030_05_pos hd hp
 · exact admission030_06_pos hd hp
 · exact admission030_07_pos hd hp
 · exact admission030_08_pos hd hp
 · exact admission030_09_pos hd hp
 · exact admission030_10_pos hd hp
 · exact admission030_11_pos hd hp
 · exact admission030_12_pos hd hp
 · exact admission030_13_pos hd hp
 · exact admission030_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission030_all
