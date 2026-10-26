/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission41_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(400951743041438293/104931017973333:ℝ),(1202140436070394880/314793053919999:ℝ)]]
theorem admission41_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission41_00_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission41_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_00_coefficients]
def admission41_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(293397449618771968/104931017973333:ℝ),(879792348856315904/314793053919999:ℝ)]]
theorem admission41_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission41_01_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission41_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_01_coefficients]
def admission41_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(492648479581420/346306990011:ℝ),(1477310282627072/1038920970033:ℝ)]]
theorem admission41_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission41_02_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission41_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_02_coefficients]
def admission41_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(43840413161661009194967040/944379161759997:ℝ),(262930397535245353948848128/2833137485279991:ℝ),(131409167057462326363947008/2833137485279991:ℝ)],
![(43821679200863936149172224/944379161759997:ℝ),(262817996904331775967236096/2833137485279991:ℝ),(131352968312539967519719424/2833137485279991:ℝ)]]
theorem admission41_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (31316988065848342781/61890832745103163392:ℝ) admission41_03_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission41_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_03_coefficients]
def admission41_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6632133298952387368/908942231:ℝ),(1683378497945580298240/115435663337:ℝ),(841097745552027680768/115435663337:ℝ)],
![(2528861226558556206964/346306990011:ℝ),(15162512862765796913152/1038920970033:ℝ),(7575930772885889613824/1038920970033:ℝ)]]
theorem admission41_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (300799994070063/3782595816226816:ℝ) admission41_04_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission41_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_04_coefficients]
def admission41_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2542464523451128180548251198/590236976099998125:ℝ),(1017028894949483941847489788/118047395219999625:ℝ),(847559839130590898984360914/196745658699999375:ℝ)],
![(2536098334857548657911540874/590236976099998125:ℝ),(5072414679049658446723692524/590236976099998125:ℝ),(33817545468188905173314722/7869826347999975:ℝ)]]
theorem admission41_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1268049167428774328955770437/27040517431887206107054080000:ℝ) admission41_05_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission41_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_05_coefficients]
def admission41_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1417658155090487634617025141273283306140909568/32998524043161039460837289280333:ℝ),(4249652608862884722351932982483472218421116928/32998524043161039460837289280333:ℝ),(4246331792857172767609453389286134509637468160/32998524043161039460837289280333:ℝ),(1414337338994639703940790538176745597357260800/32998524043161039460837289280333:ℝ)],
![(1418703194345495922819062752415879329895145472/32998524043161039460837289280333:ℝ),(4252786890238665370134146178210974111936929792/32998524043161039460837289280333:ℝ),(4249465238121192339504528111806388483779461120/32998524043161039460837289280333:ℝ),(1415381542137850890685772108162493701737676800/32998524043161039460837289280333:ℝ)]]
theorem admission41_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20581317061363947926158879100355925/180215939307716823508786049189658624:ℝ) admission41_06_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission41_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_06_coefficients]
def admission41_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(65602651712700660900998678490506318936/2943405944443942508325509703:ℝ),(43712725192897567407041183586606915584/981135314814647502775169901:ℝ),(65535532238755584172736494572897566720/2943405944443942508325509703:ℝ)],
![(65538685317905701634997572221677258044/2943405944443942508325509703:ℝ),(43670091849532840154195199070041460736/981135314814647502775169901:ℝ),(65471598599370315053712633703442677760/2943405944443942508325509703:ℝ)]]
theorem admission41_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (15609645509569720042637022424565/64299683991692738741873534631936:ℝ) admission41_07_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission41_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_07_coefficients]
def admission41_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(401476724148749904916553099389706996865058286732745816845963/435474609944587197276674531254394531250000000000:ℝ),(241444947486515603026077227225421136334032893480927603323281/87094921988917439455334906250878906250000000000:ℝ),(1210019133433962529712250054541201151398443043178296978658399/435474609944587197276674531254394531250000000000:ℝ),(404271119932420405533328409723202478185304731892928216387957/435474609944587197276674531254394531250000000000:ℝ)],
![(102321918978449416944881080489194723321520378484035492950449/108868652486146799319168632813598632812500000000:ℝ),(615324227632526961214238187593260975408951561290299750298511/217737304972293598638337265627197265625000000000:ℝ),(1233433716122327798860114084306090054752979938861036323202143/435474609944587197276674531254394531250000000000:ℝ),(412072936553270514253281620994116073565960719135231138156917/435474609944587197276674531254394531250000000000:ℝ)]]
theorem admission41_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (401476724148749904916553099389706996865058286732745816845963/163433607589646249450853051083325821681664000000000000000000000:ℝ) admission41_08_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission41_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_08_coefficients]
def admission41_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(28132253758643900913932695337609479329927335807816/8709492198891743945533490625087890625:ℝ),(84288740217351715134292024635199147165545318798944/8709492198891743945533490625087890625:ℝ),(84180734136583341556055189638617585929291974443008/8709492198891743945533490625087890625:ℝ),(5604849536299225585274783632925471090583720165376/1741898439778348789106698125017578125:ℝ)],
![(276837939185486321034127644477811743053967207364/86232596028631128173598917080078125:ℝ),(83774062700666902566462400964785331985899674211696/8709492198891743945533490625087890625:ℝ),(83666244760303287743768994699817214639903023235072/8709492198891743945533490625087890625:ℝ),(5570562784198510255000351740395774996301299580928/1741898439778348789106698125017578125:ℝ)]]
theorem admission41_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (166015707975581593960534088027351349481979/19482804249482899838787680993476608000000000:ℝ) admission41_09_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission41_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_09_coefficients]
def admission41_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(129563719305237600273786023843837550592/27667358254687412109375:ℝ),(129360468635388846130870880742724919296/9222452751562470703125:ℝ),(1033257908468185839098162456760418304/73779622012499765625:ℝ),(128954029089606073605484302900819656704/27667358254687412109375:ℝ)],
![(17216448082033639865559483298834407424/1844490550312494140625:ℝ),(773521447016796443161563818116534378496/27667358254687412109375:ℝ),(772302853713683670199153137455280422912/27667358254687412109375:ℝ),(28558680884148270203720174313473572864/3074150917187490234375:ℝ)],
![(128682608763807338904275734804728276992/27667358254687412109375:ℝ),(385438862038341341750743915876145358848/27667358254687412109375:ℝ),(76965991875566300789628908006405177344/5533471650937482421875:ℝ),(128073706118274788242301358960608804864/27667358254687412109375:ℝ)]]
theorem admission41_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (954223469780942710059146277313/422508084873237595422720000000000:ℝ) admission41_10_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission41_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_10_coefficients]
def admission41_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(53800084420402411071343935678703340456/2943405944443942508325509703:ℝ),(35848424657208519620730581872298786816/981135314814647502775169901:ℝ),(53745197570838690831730629534053040128/2943405944443942508325509703:ℝ)],
![(53746310629089759195208322217255692996/2943405944443942508325509703:ℝ),(35812584821092158830075956027024719872/981135314814647502775169901:ℝ),(53691451849575067426516979048266072064/2943405944443942508325509703:ℝ)]]
theorem admission41_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6400519829937823704065916424783/32149841995846369370936767315968:ℝ) admission41_11_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission41_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_11_coefficients]
def admission41_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission41_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission41_12_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission41_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_12_coefficients]
def admission41_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission41_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission41_13_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission41_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_13_coefficients]
def admission41_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission41_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission41_14_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission41_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_14_coefficients]
theorem admission41_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission41_00_pos hδ hp
 · exact admission41_01_pos hδ hp
 · exact admission41_02_pos hδ hp
 · exact admission41_03_pos hδ hp
 · exact admission41_04_pos hδ hp
 · exact admission41_05_pos hδ hp
 · exact admission41_06_pos hδ hp
 · exact admission41_07_pos hδ hp
 · exact admission41_08_pos hδ hp
 · exact admission41_09_pos hδ hp
 · exact admission41_10_pos hδ hp
 · exact admission41_11_pos hδ hp
 · exact admission41_12_pos hδ hp
 · exact admission41_13_pos hδ hp
 · exact admission41_14_pos hδ hp
#print axioms admission41_all
end
end LewkoStage1Finite
