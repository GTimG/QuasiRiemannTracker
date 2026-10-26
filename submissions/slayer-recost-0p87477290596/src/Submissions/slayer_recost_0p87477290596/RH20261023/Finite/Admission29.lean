/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission29_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(95703941878762633/786981005458153:ℝ),(93916960873304480/786981005458153:ℝ)]
]
theorem admission29_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission29_00_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission29_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_00_coefficients]
def admission29_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(69733568698643584/786981005458153:ℝ),(68733568698643584/786981005458153:ℝ)]
]
theorem admission29_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission29_01_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission29_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_01_coefficients]
def admission29_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35451730827454582/786981005458153:ℝ),(34970600068684672/786981005458153:ℝ)]
]
theorem admission29_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission29_02_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission29_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_02_coefficients]
def admission29_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(468649152051841125376/643893549920307:ℝ),(3390995925480620391424/2360943016374459:ℝ),(5018207103871608795136/7082829049123377:ℝ)],
  ![(5017700667977284058240/7082829049123377:ℝ),(3299445055045878913408/2360943016374459:ℝ),(4881003497160352681984/7082829049123377:ℝ)]
]
theorem admission29_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1191651244423914229/2417605648767446016:ℝ) admission29_03_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission29_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_03_coefficients]
def admission29_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(93573324154129300080/786981005458153:ℝ),(183078815099611264000/786981005458153:ℝ),(89524736175832760320/786981005458153:ℝ)],
  ![(98150775662378351590/786981005458153:ℝ),(192132022285893183616/786981005458153:ℝ),(94000972984624398336/786981005458153:ℝ)]
]
theorem admission29_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4098117195548985/50366784349321792:ℝ) admission29_04_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission29_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_04_coefficients]
def admission29_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(32489347422501524588743/491863128411345625:ℝ),(195415425380849771240458/1475589385234036875:ℝ),(97930040806437454224229/1475589385234036875:ℝ)],
  ![(2476662134861096635707/44714829855576875:ℝ),(164141560330544987362834/1475589385234036875:ℝ),(82393934015548361553253/1475589385234036875:ℝ)]
]
theorem admission29_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (7429986404583289907121/187547589722565509120000:ℝ) admission29_05_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission29_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_05_coefficients]
def admission29_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(1543243400718653235987894109130731048960/68746640427663724059495193026399:ℝ),(13561496693068034639454901644964303400960/206239921282991172178485579079197:ℝ),(13237053117183556771657347905682265210880/206239921282991172178485579079197:ℝ),(12928761621282925919144169934264729600/619339102951925441977434171409:ℝ)],
  ![(1611350258885257920514170377738456945152/68746640427663724059495193026399:ℝ),(14169247885934321230964420256226343237120/206239921282991172178485579079197:ℝ),(1258149875415660899366907826642720866304/18749083752999197470771416279927:ℝ),(13526853719969514194581618528705576960/619339102951925441977434171409:ℝ)]
]
theorem admission29_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9247370925867266120298507166575/79275405177846456573111573940352:ℝ) admission29_06_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission29_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_06_coefficients]
def admission29_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1958884665085882152485231231898673040/5574051926567328977796907542681:ℝ),(428554233506024525903489857674132480/619339102951925441977434171409:ℝ),(1898344172495916360040280520129863680/5574051926567328977796907542681:ℝ)],
  ![(1838702751460005737745335895482889722/5574051926567328977796907542681:ℝ),(402064217405654327448017673273232768/619339102951925441977434171409:ℝ),(1780108203274717417200401456592363520/5574051926567328977796907542681:ℝ)]
]
theorem admission29_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (217298364657558278466845880931685/951304862134157478877338887284224:ℝ) admission29_07_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission29_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_07_coefficients]
def admission29_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2355759761773695007974135826754743565507967771135164837/3628940056358938136586528348099609375000000000000:ℝ),(22066290204994398676872125387418666132213171769189315601/10886820169076814409759585044298828125000000000000:ℝ),(22930574129095661190883264675533414921270889773428768819/10886820169076814409759585044298828125000000000000:ℝ),(881275132632116725724599230928355581562334660293883081/1209646685452979378862176116033203125000000000000:ℝ)],
  ![(88295700560733136584157643278556110905252205591394737081/72578801127178762731730566961992187500000000000000:ℝ),(807418406120809642797126743466582861348570156463270340179/217736403381536288195191700885976562500000000000000:ℝ),(205052123116159621585148838963912651321288094305217115359/54434100845384072048797925221494140625000000000000:ℝ),(12341129075710918429532995181299937866496282015301437/9677173483623835030897408928265625000000000000:ℝ)]
]
theorem admission29_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2355759761773695007974135826754743565507967771135164837/649424119216918172246930013719363584000000000000000000000:ℝ) admission29_08_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission29_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_08_coefficients]
def admission29_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(18818346972055767806853396812705399938024724/10886820169076814409759585044298828125:ℝ),(10917703272759472922944854444946521666124916/2177364033815362881951917008859765625:ℝ),(17576435852770136633799515246543361243767296/3628940056358938136586528348099609375:ℝ),(16959210520631352522741234840289287057452032/10886820169076814409759585044298828125:ℝ)],
  ![(120473067994899239329227701119704702271229309/108868201690768144097595850442988281250:ℝ),(31371430336738458027814697099001301354167707/9897109244615285827054168222089843750:ℝ),(54801256723772753403155696788200644102307008/18144700281794690682932641740498046875:ℝ),(10419561626255375059163925001492997210641408/10886820169076814409759585044298828125:ℝ)]
]
theorem admission29_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10175353150640014706214770509270505088517/1902609724268314957754677774568448000000000:ℝ) admission29_09_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission29_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_09_coefficients]
def admission29_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(312115656429897401778677407744/7685361381427275390625:ℝ),(8089882117494212967005932249088/69168252432845478515625:ℝ),(7753580564875817105787574489088/69168252432845478515625:ℝ),(824249639250226918263246303232/23056084144281826171875:ℝ)],
  ![(4482733084858976361494692815872/69168252432845478515625:ℝ),(4268680460867394348466838254592/23056084144281826171875:ℝ),(4055173625817030364143383693312/23056084144281826171875:ℝ),(3842232182832884408524329132032/69168252432845478515625:ℝ)],
  ![(328543121760557407363121524288/13833650486569095703125:ℝ),(4624248419431734781006082209984/69168252432845478515625:ℝ),(4321041720371567680903996555648/69168252432845478515625:ℝ),(1339518956344182436713521967104/69168252432845478515625:ℝ)]
]
theorem admission29_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (327030995201216415213262199/257877935868527575040000000000:ℝ) admission29_10_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission29_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_10_coefficients]
def admission29_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1606383183133053631081709266921472624/5574051926567328977796907542681:ℝ),(3163066130070216076491971782724712448/5574051926567328977796907542681:ℝ),(1556912991155946672966344776379469824/5574051926567328977796907542681:ℝ)],
  ![(1505319334731633405688621102238779526/5574051926567328977796907542681:ℝ),(2962615365724709941756246265220404992/5574051926567328977796907542681:ℝ),(1457518069972897353347232163903041536/5574051926567328977796907542681:ℝ)]
]
theorem admission29_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (355839372551976892907039102515391/1902609724268314957754677774568448:ℝ) admission29_11_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission29_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_11_coefficients]
def admission29_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission29_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission29_12_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission29_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_12_coefficients]
def admission29_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission29_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission29_13_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission29_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_13_coefficients]
def admission29_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission29_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission29_14_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission29_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_14_coefficients]
theorem admission29_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission29_00_pos hδ hp
 · exact admission29_01_pos hδ hp
 · exact admission29_02_pos hδ hp
 · exact admission29_03_pos hδ hp
 · exact admission29_04_pos hδ hp
 · exact admission29_05_pos hδ hp
 · exact admission29_06_pos hδ hp
 · exact admission29_07_pos hδ hp
 · exact admission29_08_pos hδ hp
 · exact admission29_09_pos hδ hp
 · exact admission29_10_pos hδ hp
 · exact admission29_11_pos hδ hp
 · exact admission29_12_pos hδ hp
 · exact admission29_13_pos hδ hp
 · exact admission29_14_pos hδ hp
#print axioms admission29_all
end
end RH20261023Finite
