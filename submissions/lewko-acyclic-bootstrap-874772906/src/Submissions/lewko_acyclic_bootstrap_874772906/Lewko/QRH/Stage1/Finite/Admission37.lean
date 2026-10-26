/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission37_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(100416634023839573/104931017973333:ℝ),(300535109017598720/314793053919999:ℝ)]]
theorem admission37_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission37_00_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission37_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_00_coefficients]
def admission37_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(73449362404692992/104931017973333:ℝ),(219948087214078976/314793053919999:ℝ)]]
theorem admission37_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission37_01_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission37_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_01_coefficients]
def admission37_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(123320908924652/346306990011:ℝ),(369327570656768/1038920970033:ℝ)]]
theorem admission37_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission37_02_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission37_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_02_coefficients]
def admission37_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(688075699198689547304960/944379161759997:ℝ),(4121444560721270847586304/2833137485279991:ℝ),(2057219709525202205671424/2833137485279991:ℝ)],
![(686904631457068713620480/944379161759997:ℝ),(4114418932338760918768640/2833137485279991:ℝ),(2053707287967554777907200/2833137485279991:ℝ)]]
theorem admission37_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (7834271575803965675/15472708186275790848:ℝ) admission37_03_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission37_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_03_coefficients]
def admission37_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(39553322932384808768/346306990011:ℝ),(78885099784575598592/346306990011:ℝ),(39331908964663164928/346306990011:ℝ)],
![(39679741573245462572/346306990011:ℝ),(237412746073505170432/1038920970033:ℝ),(118373918326342025216/1038920970033:ℝ)]]
theorem admission37_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9377457848707/118206119257088:ℝ) admission37_04_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission37_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_04_coefficients]
def admission37_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8033831274778628491465426/118047395219999625:ℝ),(80350971253577482115409332/590236976099998125:ℝ),(4464634073743248371133578/65581886233333125:ℝ)],
![(7954157091996372333807982/118047395219999625:ℝ),(3182195002329558793795988/23609479043999925:ℝ),(98232052367503542668018/1457375249629625:ℝ)]]
theorem admission37_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (3977078545998186166903991/84501616974647519084544000:ℝ) admission37_05_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission37_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_05_coefficients]
def admission37_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5564376540152155255533515780661825570832384/32998524043161039460837289280333:ℝ),(16641206605944709903208999816005425471913984/32998524043161039460837289280333:ℝ),(130624791835715082874715313797055329075200/259830897977645980006592828979:ℝ),(5512518474863305248850960266482426891468800/32998524043161039460837289280333:ℝ)],
![(5580744523293747403851661707536808107591680/32998524043161039460837289280333:ℝ),(16690258176924751796148377640523140083107840/32998524043161039460837289280333:ℝ),(16638347825122965632517981730496072997928960/32998524043161039460837289280333:ℝ),(5528834148975980041741297297509741022412800/32998524043161039460837289280333:ℝ)]]
theorem admission37_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (641741612328135553846480355887025/5631748103366150734649564037176832:ℝ) admission37_06_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission37_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_06_coefficients]
def admission37_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1032696850140000577925795933783804864/2943405944443942508325509703:ℝ),(687060925356625887557580973363904512/981135314814647502775169901:ℝ),(1028488025249832737630372945085071360/2943405944443942508325509703:ℝ)],
![(1028692805761463751377233088158642340/2943405944443942508325509703:ℝ),(684394294438602714224067452904401920/981135314814647502775169901:ℝ),(1024492172788253417691381640744140800/2943405944443942508325509703:ℝ)]]
theorem admission37_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3908127490189565344586874545075/16074920997923184685468383657984:ℝ) admission37_07_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission37_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_07_coefficients]
def admission37_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(146003501605046689984644727971666646750728497240164350611/43547460994458719727667453125439453125000000000:ℝ),(2212321909043327457232360995058767814290895220443374382753/217737304972293598638337265627197265625000000000:ℝ),(2234585639587298859463611352099031085004194144080513108323/217737304972293598638337265627197265625000000000:ℝ),(6018249691361720808897995904374395110696283472453683829/1741898439778348789106698125017578125000000000:ℝ)],
![(253201565124099770990919406409551378150284799603363465769/69675937591133951564267925000703125000000000000:ℝ),(3833196923991836339814825278443949767023490377357128542429/348379687955669757821339625003515625000000000000:ℝ),(483545223489038050192530422953139427926219606238338687687/43547460994458719727667453125439453125000000000:ℝ),(162646580754121315097376790220162370549682066877440410989/43547460994458719727667453125439453125000000000:ℝ)]]
theorem admission37_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (146003501605046689984644727971666646750728497240164350611/63841252964705566191739473079424149094400000000000000000000:ℝ) admission37_08_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission37_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_08_coefficients]
def admission37_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22837829855640212057541577684379999356331889664/1741898439778348789106698125017578125:ℝ),(340860548034180777144494335237934982015230676416/8709492198891743945533490625087890625:ℝ),(339154599430196376079893925933972453158700384256/8709492198891743945533490625087890625:ℝ),(22496640315439236607459871676988685604900831232/1741898439778348789106698125017578125:ℝ)],
![(22299745887388825412153503222277389726988178112/1741898439778348789106698125017578125:ℝ),(659012014367428544548082666098599449005337252/17246519205726225634719783416015625:ℝ),(13244275439340339176448666667755672554568716288/348379687955669757821339625003515625:ℝ),(878436392554622382876874934248487365269520384/69675937591133951564267925000703125:ℝ)]]
theorem admission37_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1675484452351803556207418316361403208293/194828042494828998387876809934766080000000:ℝ) admission37_09_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission37_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_09_coefficients]
def admission37_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(26437209555954834434792425893527552/5533471650937482421875:ℝ),(43795159068740174594970956189007872/3074150917187490234375:ℝ),(43528411168591132493357453435469824/3074150917187490234375:ℝ),(129785317609284793259440604685795328/27667358254687412109375:ℝ)],
![(17396069832045804132017175496835072/1844490550312494140625:ℝ),(155606392272980318376936467602849792/5533471650937482421875:ℝ),(154648545987904576761898563094183936/5533471650937482421875:ℝ),(3415357572266611385400908132122624/368898110062498828125:ℝ)],
![(41199627911842593415365631742464/8853554641499971875:ℝ),(122834261793377007747774890357248/8853554641499971875:ℝ),(122069949934865978810530525487104/8853554641499971875:ℝ),(8087063270431937895624253374464/1770710928299994375:ℝ)]]
theorem admission37_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3856212268081635425388457/1690032339492950381690880000:ℝ) admission37_10_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission37_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_10_coefficients]
def admission37_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(846990170870327599720532023227593792/2943405944443942508325509703:ℝ),(563511955898785180115541131131813888/981135314814647502775169901:ℝ),(843547708070703064924875886251474944/2943405944443942508325509703:ℝ)],
![(843624042608699337125148315391427420/2943405944443942508325509703:ℝ),(561270212027647908103590980536668160/981135314814647502775169901:ℝ),(840188600491726602099022730889789440/2943405944443942508325509703:ℝ)]]
theorem admission37_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1602532578452542499731107198505/8037460498961592342734191828992:ℝ) admission37_11_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission37_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_11_coefficients]
def admission37_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission37_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission37_12_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission37_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_12_coefficients]
def admission37_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission37_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission37_13_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission37_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_13_coefficients]
def admission37_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission37_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission37_14_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission37_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_14_coefficients]
theorem admission37_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission37_00_pos hδ hp
 · exact admission37_01_pos hδ hp
 · exact admission37_02_pos hδ hp
 · exact admission37_03_pos hδ hp
 · exact admission37_04_pos hδ hp
 · exact admission37_05_pos hδ hp
 · exact admission37_06_pos hδ hp
 · exact admission37_07_pos hδ hp
 · exact admission37_08_pos hδ hp
 · exact admission37_09_pos hδ hp
 · exact admission37_10_pos hδ hp
 · exact admission37_11_pos hδ hp
 · exact admission37_12_pos hδ hp
 · exact admission37_13_pos hδ hp
 · exact admission37_14_pos hδ hp
#print axioms admission37_all
end
end LewkoStage1Finite
