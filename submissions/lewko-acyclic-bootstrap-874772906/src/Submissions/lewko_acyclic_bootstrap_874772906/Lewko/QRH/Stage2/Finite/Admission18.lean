/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission18_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission18_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission18_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission18_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_00_coefficients]
def admission18_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission18_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission18_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission18_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_01_coefficients]
def admission18_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission18_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission18_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission18_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_02_coefficients]
def admission18_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1820812579346714645248/157396201727529:ℝ),(32555059921915775052544/1416565815547761:ℝ),(16168025707795343245312/1416565815547761:ℝ)],
![(602868665519911293952/52465400575843:ℝ),(32335435990901341084672/1416565815547761:ℝ),(16058262821863736147968/1416565815547761:ℝ)]]
theorem admission18_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (245029645109004763/483521131706969088:ℝ) admission18_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission18_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_03_coefficients]
def admission18_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(94595693366009493230/52465400575843:ℝ),(187099616268154958080/52465400575843:ℝ),(92508894586652753920/52465400575843:ℝ)],
![(95802819739897636760/52465400575843:ℝ),(189500373722615993344/52465400575843:ℝ),(93702557742609563648/52465400575843:ℝ)]]
theorem admission18_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8469442253416695/107449140379326464:ℝ) admission18_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission18_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_04_coefficients]
def admission18_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(324622063969973042625982/295117878239116875:ℝ),(649579155563631321634504/295117878239116875:ℝ),(108314550435268259329924/98372626079705625:ℝ)],
![(312112431169727561322868/295117878239116875:ℝ),(624640723973849029822168/295117878239116875:ℝ),(4166863544063112383524/3934905043188225:ℝ)]]
theorem admission18_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (78028107792431890330717/1650418796226454487040000:ℝ) admission18_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission18_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_05_coefficients]
def admission18_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5553934624294290272644829769294966553600/8249596917978249986997496465053:ℝ),(16458280338878316008842705823455992478720/8249596917978249986997496465053:ℝ),(16255770784853854352343209701913424363520/8249596917978249986997496465053:ℝ),(5351423674280264668417059647752398438400/8249596917978249986997496465053:ℝ)],
![(5618487903042117916578957525133023096832/8249596917978249986997496465053:ℝ),(16651115239219186023971128147389744001024/8249596917978249986997496465053:ℝ),(16447785110285427193247868947738948534272/8249596917978249986997496465053:ℝ),(5415156369112410854593693525482227630080/8249596917978249986997496465053:ℝ)]]
theorem admission18_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1275878828592363516906990920961475/11263449658679637315580581840285696:ℝ) admission18_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission18_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_06_coefficients]
def admission18_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(417989769835830826942574050373846770/74320692954759008891869337523:ℝ),(829262427830017716100651805741843200/74320692954759008891869337523:ℝ),(411286013111931037629521022887198720/74320692954759008891869337523:ℝ)],
![(411632062727962990169447602414580200/74320692954759008891869337523:ℝ),(816598905465419206022261971329793024/74320692954759008891869337523:ℝ),(404980094682616933134349491020103680/74320692954759008891869337523:ℝ)]]
theorem admission18_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3089752919636664834093852928315/12684064930945537517545700270592:ℝ) admission18_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission18_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_07_coefficients]
def admission18_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(715411879776802004725674212780824914234108457328382317/69675649645086570836127503927812500000000000000:ℝ),(11317518137792118369267418296021631006867570086759041503/348378248225432854180637519639062500000000000000:ℝ),(11903200932035255957205843202694113624941416518647069853/348378248225432854180637519639062500000000000000:ℝ),(832546280635231198406713853438337815108139931205987987/69675649645086570836127503927812500000000000000:ℝ)],
![(25647513110445994037291895706575007013666282914791280931/1741891241127164270903187598195312500000000000000:ℝ),(79730379043251064074506464281378277344262778231954329049/1741891241127164270903187598195312500000000000000:ℝ),(82515513636785962030243495574831492819704377889998679313/1741891241127164270903187598195312500000000000000:ℝ),(5686518681232599736365892717889210783384315264567126239/348378248225432854180637519639062500000000000000:ℝ)]]
theorem admission18_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (715411879776802004725674212780824914234108457328382317/399006182070934438439940006208088309760000000000000000000:ℝ) admission18_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission18_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_08_coefficients]
def admission18_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(25172347586893238892224599362045610316071309/435472810281791067725796899548828125:ℝ),(74142071182068131538936945920808126411465631/435472810281791067725796899548828125:ℝ),(72770189509116602695489815205677729211277056/435472810281791067725796899548828125:ℝ),(23800477128821423614418210221841808447913984/435472810281791067725796899548828125:ℝ)],
![(115213900722059794155936078975397642925724308/2177364051408955338628984497744140625:ℝ),(338951956935522769994724615849958314368454812/2177364051408955338628984497744140625:ℝ),(332276947096483214938558405305380380303760384/2177364051408955338628984497744140625:ℝ),(21707789463837824053760139400283611912830976/435472810281791067725796899548828125:ℝ)]]
theorem admission18_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (662469160883722657890629254159045773707/76104389585673225105274201623552000000000:ℝ) admission18_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission18_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_09_coefficients]
def admission18_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73954366308948663053988364457344/13833650542458603515625:ℝ),(217065448648344470588898169768832/13833650542458603515625:ℝ),(212275754331489659625867996165632/13833650542458603515625:ℝ),(69164700709476664590958190854144/13833650542458603515625:ℝ)],
![(141233051217083539473807514590208/13833650542458603515625:ℝ),(414198420498797174659297297255424/13833650542458603515625:ℝ),(404713241618662547389970050740224/13833650542458603515625:ℝ),(131747930142261412204480268075008/13833650542458603515625:ℝ)],
![(22409978281622848672504407033856/4611216847486201171875:ℝ),(65662510489007133403235984779264/4611216847486201171875:ℝ),(12819523604768678549461541691392/922243369497240234375:ℝ),(20845095512834108016576130711552/4611216847486201171875:ℝ)]]
theorem admission18_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (39758864427250114472534429/17191862460692234240000000000:ℝ) admission18_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission18_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_10_coefficients]
def admission18_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(114309681895416418138069836472103770/24773564318253002963956445841:ℝ),(680358747235937055298679822586795520/74320692954759008891869337523:ℝ),(37493611584145413042048739902914560/8257854772751000987985481947:ℝ)],
![(112527861725553115042013782303387144/24773564318253002963956445841:ℝ),(669712330942819512697182884937054208/74320692954759008891869337523:ℝ),(36904604637473485995468669932994560/8257854772751000987985481947:ℝ)]]
theorem admission18_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (563119577598167205741404265335/2818681095765675003899044504576:ℝ) admission18_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission18_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_11_coefficients]
def admission18_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission18_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission18_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission18_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_12_coefficients]
def admission18_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission18_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission18_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission18_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_13_coefficients]
def admission18_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission18_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission18_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission18_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_14_coefficients]
theorem admission18_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission18_00_pos hδ hp
 · exact admission18_01_pos hδ hp
 · exact admission18_02_pos hδ hp
 · exact admission18_03_pos hδ hp
 · exact admission18_04_pos hδ hp
 · exact admission18_05_pos hδ hp
 · exact admission18_06_pos hδ hp
 · exact admission18_07_pos hδ hp
 · exact admission18_08_pos hδ hp
 · exact admission18_09_pos hδ hp
 · exact admission18_10_pos hδ hp
 · exact admission18_11_pos hδ hp
 · exact admission18_12_pos hδ hp
 · exact admission18_13_pos hδ hp
 · exact admission18_14_pos hδ hp
#print axioms admission18_all
end
end LewkoStage2Finite
