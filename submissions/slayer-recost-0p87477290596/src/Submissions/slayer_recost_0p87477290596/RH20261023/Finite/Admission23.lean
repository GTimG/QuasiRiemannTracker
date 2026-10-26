/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission23_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(189620902752067113/786981005458153:ℝ),(187833921746608960/786981005458153:ℝ)]
]
theorem admission23_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission23_00_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission23_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_00_coefficients]
def admission23_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(138467137397287168/786981005458153:ℝ),(137467137397287168/786981005458153:ℝ)]
]
theorem admission23_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission23_01_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission23_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_01_coefficients]
def admission23_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(70422330896139254/786981005458153:ℝ),(69941200137369344/786981005458153:ℝ)]
]
theorem admission23_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission23_02_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission23_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_02_coefficients]
def admission23_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(53891500318890001043200/2360943016374459:ℝ),(321156646426871435668736/7082829049123377:ℝ),(159484998470201432539136/7082829049123377:ℝ)],
  ![(53708401578020518087168/2360943016374459:ℝ),(320058526777417962348032/7082829049123377:ℝ),(158936184043356408086528/7082829049123377:ℝ)]
]
theorem admission23_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (4850347413432507571/9670422595069784064:ℝ) admission23_03_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission23_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_03_coefficients]
def admission23_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2901951737779368595870/786981005458153:ℝ),(5739733356102737036544/786981005458153:ℝ),(2837934136773898502144/786981005458153:ℝ)],
  ![(2920058633282691205012/786981005458153:ℝ),(525067701610042493440/71543727768923:ℝ),(259621734909915004928/71543727768923:ℝ)]
]
theorem admission23_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (259820630197805649/3223474198356594688:ℝ) admission23_04_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission23_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_04_coefficients]
def admission23_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2996027968342390743249956/1475589385234036875:ℝ),(1199647080630102364225276/295117877046807375:ℝ),(90971818091693248867278/44714829855576875:ℝ)],
  ![(2933479804684108481913458/1475589385234036875:ℝ),(5873543245886345882687228/1475589385234036875:ℝ),(195995037990821389462418/98372625682269125:ℝ)]
]
theorem admission23_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1466739902342054240956729/33008375791171529605120000:ℝ) admission23_05_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission23_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_05_coefficients]
def admission23_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(283416941238857387363292600353311907732480/206239921282991172178485579079197:ℝ),(2522313163144786161961817623091300322304/619339102951925441977434171409:ℝ),(829661205110381835019692299191755390779392/206239921282991172178485579079197:ℝ),(820263638577868199519977492659652526080/619339102951925441977434171409:ℝ)],
  ![(285030773187474835025480256339733591746560/206239921282991172178485579079197:ℝ),(93861239530630780108460320083685617477632/22915546809221241353165064342133:ℝ),(834461563186288294253854896524691674103808/206239921282991172178485579079197:ℝ),(825048375367360905723477081415179304960/619339102951925441977434171409:ℝ)]
]
theorem admission23_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (586698273595238828315718764776935/5073625931382173220679140732182528:ℝ) admission23_06_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission23_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_06_coefficients]
def admission23_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(20259833403971798846498284892233323926/1858017308855776325932302514227:ℝ),(120578676875963275568470400327829294848/5574051926567328977796907542681:ℝ),(59801125766099731978569944135855636480/5574051926567328977796907542681:ℝ)],
  ![(20100890728054996465271943539046196964/1858017308855776325932302514227:ℝ),(119628912709271816224912384754463099392/5574051926567328977796907542681:ℝ),(59328181889214936207210427881705635840/5574051926567328977796907542681:ℝ)]
]
theorem admission23_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (905276212909163455310217710597315/3805219448536629915509355549136896:ℝ) admission23_07_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission23_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_07_coefficients]
def admission23_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(7867292815339801106530220624636248362004417324729146401603/217736403381536288195191700885976562500000000000000:ℝ),(537976130824919677396663600426102312423266831355877346257/4838586741811917515448704464132812500000000000000:ℝ),(24815659933655332659456263124512277601994174319445052775479/217736403381536288195191700885976562500000000000000:ℝ),(8474013069880020707620295370105152893585567647222218595517/217736403381536288195191700885976562500000000000000:ℝ)],
  ![(8837569823548940401620924232941968523668683284558381213761/217736403381536288195191700885976562500000000000000:ℝ),(3011308268074713088407259768895979994198248424347880138403/24192933709059587577243522320664062500000000000000:ℝ),(27690598537142809557956757734037941997212465924350825650743/217736403381536288195191700885976562500000000000000:ℝ),(9426380112517737939892811610202309672105136499153285618877/217736403381536288195191700885976562500000000000000:ℝ)]
]
theorem admission23_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (7867292815339801106530220624636248362004417324729146401603/2493788617792965781428211252682356162560000000000000000000000:ℝ) admission23_08_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission23_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_08_coefficients]
def admission23_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(5214473261482204900830353561266118597964057199/54434100845384072048797925221494140625:ℝ),(15332071608497588147529328262680260276799601981/54434100845384072048797925221494140625:ℝ),(5007123645012536577335799189795937095039958784/18144700281794690682932641740498046875:ℝ),(980755091010390922038202072357773734127960064/10886820169076814409759585044298828125:ℝ)],
  ![(4948277333560336700924647713155758129620706186/54434100845384072048797925221494140625:ℝ),(1321646512841047550780965941820351442507866234/4948554622307642913527084111044921875:ℝ),(4744006976964705309000885475241946649637628416/18144700281794690682932641740498046875:ℝ),(928437899855383102329583593647403415353475072/10886820169076814409759585044298828125:ℝ)]
]
theorem admission23_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (56667352286095160054295873635705774862883/7610438897073259831018711098273792000000000:ℝ) admission23_09_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission23_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_09_coefficients]
def admission23_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1204481424444689511711761637279104/69168252432845478515625:ℝ),(391589932124101138666001408745344/7685361381427275390625:ℝ),(687061588422790506317793007115776/13833650486569095703125:ℝ),(1115480578020520857806713994149888/69168252432845478515625:ℝ)],
  ![(42523518743133344668395893136896/1257604589688099609375:ℝ),(759901464963278763091789230402048/7685361381427275390625:ℝ),(6662108889940140360627238699649024/69168252432845478515625:ℝ),(2161790441089684199562909748559872/69168252432845478515625:ℝ)],
  ![(126007595123648818835688149792256/7685361381427275390625:ℝ),(368230732626667021856914740514304/7685361381427275390625:ℝ),(215071852116834449947404434991104/4611216828856365234375:ℝ),(348690049533086390673342402789376/23056084144281826171875:ℝ)]
]
theorem admission23_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7980881871027062774810998599/4126046973896441200640000000000:ℝ) admission23_10_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission23_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_10_coefficients]
def admission23_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(49825728613002671691181733242666959934/5574051926567328977796907542681:ℝ),(98849920591061406617873781323424286208/5574051926567328977796907542681:ℝ),(49026056347525898977970131944331608064/5574051926567328977796907542681:ℝ)],
  ![(49424819079072696011433806948003531092/5574051926567328977796907542681:ℝ),(98051439377638197069925879838509958144/5574051926567328977796907542681:ℝ),(48628476662793701699493681494425894912/5574051926567328977796907542681:ℝ)]
]
theorem admission23_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1484023335656546072372243697950009/7610438897073259831018711098273792:ℝ) admission23_11_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission23_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_11_coefficients]
def admission23_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission23_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission23_12_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission23_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_12_coefficients]
def admission23_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission23_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission23_13_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission23_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_13_coefficients]
def admission23_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission23_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission23_14_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission23_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_14_coefficients]
theorem admission23_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission23_00_pos hδ hp
 · exact admission23_01_pos hδ hp
 · exact admission23_02_pos hδ hp
 · exact admission23_03_pos hδ hp
 · exact admission23_04_pos hδ hp
 · exact admission23_05_pos hδ hp
 · exact admission23_06_pos hδ hp
 · exact admission23_07_pos hδ hp
 · exact admission23_08_pos hδ hp
 · exact admission23_09_pos hδ hp
 · exact admission23_10_pos hδ hp
 · exact admission23_11_pos hδ hp
 · exact admission23_12_pos hδ hp
 · exact admission23_13_pos hδ hp
 · exact admission23_14_pos hδ hp
#print axioms admission23_all
end
end RH20261023Finite
