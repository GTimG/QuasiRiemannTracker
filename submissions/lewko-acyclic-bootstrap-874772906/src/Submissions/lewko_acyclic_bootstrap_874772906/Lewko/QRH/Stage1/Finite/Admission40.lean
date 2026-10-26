/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission40_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(601785011089117439/314793053919999:ℝ),(601070218035197440/314793053919999:ℝ)]]
theorem admission40_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission40_00_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission40_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_00_coefficients]
def admission40_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(440296174428157952/314793053919999:ℝ),(439896174428157952/314793053919999:ℝ)]]
theorem admission40_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission40_01_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission40_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_01_coefficients]
def admission40_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(739290297430724/1038920970033:ℝ),(738655141313536/1038920970033:ℝ)]]
theorem admission40_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission40_02_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission40_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_02_coefficients]
def admission40_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16457678662420613528496128/2833137485279991:ℝ),(10962444154187017250584576/944379161759997:ℝ),(16429658303740438223257600/2833137485279991:ℝ)],
![(16443627409255593670860800/2833137485279991:ℝ),(10953077173188480727687168/944379161759997:ℝ),(16415608617509848512200704/2833137485279991:ℝ)]]
theorem admission40_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3913786081674062851/7736354093137895424:ℝ) admission40_03_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission40_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_03_coefficients]
def admission40_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(105433058191084983404/115435663337:ℝ),(210570188098388154368/115435663337:ℝ),(105137218194003460096/115435663337:ℝ)],
![(316804139264825905712/346306990011:ℝ),(1898159352054460260352/1038920970033:ℝ),(947747729475441262592/1038920970033:ℝ)]]
theorem admission40_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (300799994070063/3782595816226816:ℝ) admission40_04_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission40_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_04_coefficients]
def admission40_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21212852237799147531376436/39349131739999875:ℝ),(636439641047524678844587216/590236976099998125:ℝ),(318246640528278050005883176/590236976099998125:ℝ)],
![(105533530334295706450731592/196745658699999375:ℝ),(633256546837446452064948304/590236976099998125:ℝ),(316655738708876847767263528/590236976099998125:ℝ)]]
theorem admission40_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (13191691291786963306341449/281672056582158396948480000:ℝ) admission40_05_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission40_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_05_coefficients]
def admission40_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(88811315749504251175411590040493812335030272/32998524043161039460837289280333:ℝ),(88672818354307644391506041402491408900132864/10999508014387013153612429760111:ℝ),(265603223045651651462283447752627014200197120/32998524043161039460837289280333:ℝ),(88396083687164981496299408636046599834828800/32998524043161039460837289280333:ℝ)],
![(88942050239725710116988587701183869819305984/32998524043161039460837289280333:ℝ),(88803483099169222049151816518584575176654848/10999508014387013153612429760111:ℝ),(7189054275214928362342811882109053205217280/891852001166514580022629440009:ℝ),(88526609080066379839422104884265112882380800/32998524043161039460837289280333:ℝ)]]
theorem admission40_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20581317061363947926158879100355925/180215939307716823508786049189658624:ℝ) admission40_06_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission40_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_06_coefficients]
def admission40_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8212719343983182236749504681251099180/2943405944443942508325509703:ℝ),(16408652539907438151974746655412656128/2943405944443942508325509703:ℝ),(8195937382306027341531053125953126400/2943405944443942508325509703:ℝ)],
![(8196719554388996570261409969906498320/2943405944443942508325509703:ℝ),(16376669344552981832217700315291918336/2943405944443942508325509703:ℝ),(8179953972459710061775087908589404160/2943405944443942508325509703:ℝ)]]
theorem admission40_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1950253003230025783008357979915/8037460498961592342734191828992:ℝ) admission40_07_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission40_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_07_coefficients]
def admission40_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(11113315479776968578036181241085278746061778686664250362179/193544271086483198789633125001953125000000000000:ℝ),(100485656368505022216190106637094703471941887885220601034871/580632813259449596368899375005859375000000000000:ℝ),(302854251925250237786566651011176438565368663179076929893871/1741898439778348789106698125017578125000000000000:ℝ),(101417121702299860410144746108459860048034746476440255048869/1741898439778348789106698125017578125000000000000:ℝ)],
![(11547765010130240982879718605406073529708945411469754308997/193544271086483198789633125001953125000000000000:ℝ),(104392654775003835342984185135569745024404387835186821543933/580632813259449596368899375005859375000000000000:ℝ),(12582644387293613754180034554787797953956863119934475671367/69675937591133951564267925000703125000000000000:ℝ),(105318030012724914770121351743916657738362740097591715933349/1741898439778348789106698125017578125000000000000:ℝ)]]
theorem admission40_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (11113315479776968578036181241085278746061778686664250362179/4539822433045729151412584752314606157824000000000000000000000:ℝ) admission40_08_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission40_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_08_coefficients]
def admission40_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1770375416979168142857250312750706413663050674188/8709492198891743945533490625087890625:ℝ),(1765873291839942563940152784878771500226819464328/2903164066297247981844496875029296875:ℝ),(5284117241839604019377928998582864137934143799296/8709492198891743945533490625087890625:ℝ),(14054982280873958126029998947975797844312326144/69675937591133951564267925000703125:ℝ)],
![(1748899150404725565636230100738087958588500167056/8709492198891743945533490625087890625:ℝ),(1744412715042869023261394730112137459590857702496/2903164066297247981844496875029296875:ℝ),(5219782557958431810570940062375951492366444593152/8709492198891743945533490625087890625:ℝ),(347088713009259536866445987133182934322505580544/1741898439778348789106698125017578125:ℝ)]]
theorem admission40_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (20688099444464417509224771686386044879109/2435350531185362479848460124184576000000000:ℝ) admission40_09_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission40_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_09_coefficients]
def admission40_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4081690228558973968914454388669830144/27667358254687412109375:ℝ),(4068984488505867226474186763170290688/9222452751562470703125:ℝ),(4056281320704987463635740319350751232/9222452751562470703125:ℝ),(4043580728897665196024115057211211776/27667358254687412109375:ℝ)],
![(8108286400202198632188727931608358912/27667358254687412109375:ℝ),(8082907741637633533589370279668523008/9222452751562470703125:ℝ),(24172602636150032774534673210546061312/27667358254687412109375:ℝ),(35698514750790991915356845791772672/122966036687499609375:ℝ)],
![(161061878997556978718399282022006784/1106694330187496484375:ℝ),(4013874090782388987401597834166255616/9222452751562470703125:ℝ),(12003611290009539980963998327907024896/27667358254687412109375:ℝ),(3988535996348611736719186875958427648/27667358254687412109375:ℝ)]]
theorem admission40_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (14858454452263607594069789633/6601688826144337428480000000000:ℝ) admission40_10_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission40_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_10_coefficients]
def admission40_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6735232521228628636916213282245895636/2943405944443942508325509703:ℝ),(13456737315354669933266985331434201088/2943405944443942508325509703:ℝ),(6721508803933812816792181847118315520/2943405944443942508325509703:ℝ)],
![(6721782053774612095459125967262606576/2943405944443942508325509703:ℝ),(13429850421811940449891871806416584704/2943405944443942508325509703:ℝ),(6708072373617906965488769225671573504/2943405944443942508325509703:ℝ)]]
theorem admission40_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (799664541914213534055801537713/4018730249480796171367095914496:ℝ) admission40_11_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission40_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_11_coefficients]
def admission40_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission40_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission40_12_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission40_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_12_coefficients]
def admission40_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission40_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission40_13_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission40_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_13_coefficients]
def admission40_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission40_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission40_14_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission40_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_14_coefficients]
theorem admission40_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission40_00_pos hδ hp
 · exact admission40_01_pos hδ hp
 · exact admission40_02_pos hδ hp
 · exact admission40_03_pos hδ hp
 · exact admission40_04_pos hδ hp
 · exact admission40_05_pos hδ hp
 · exact admission40_06_pos hδ hp
 · exact admission40_07_pos hδ hp
 · exact admission40_08_pos hδ hp
 · exact admission40_09_pos hδ hp
 · exact admission40_10_pos hδ hp
 · exact admission40_11_pos hδ hp
 · exact admission40_12_pos hδ hp
 · exact admission40_13_pos hδ hp
 · exact admission40_14_pos hδ hp
#print axioms admission40_all
end
end LewkoStage1Finite
