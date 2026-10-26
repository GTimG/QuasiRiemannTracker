/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def admission31_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(411927445267109/3328741896069:ℝ), (404598703371040/3328741896069:ℝ)]]
theorem admission31_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (12643709480345/13314967584276:ℝ) admission31_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission31_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_00_coefficients]
def admission31_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(302078962696832/3328741896069:ℝ), (298078962696832/3328741896069:ℝ)]]
theorem admission31_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2328741896069/3328741896069:ℝ) admission31_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission31_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_01_coefficients]
def admission31_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(152940370065076/3328741896069:ℝ), (151001689055936/3328741896069:ℝ)]]
theorem admission31_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2359401391499/6657483792138:ℝ) admission31_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission31_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_02_coefficients]
def admission31_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21938698502714186368/29958677064621:ℝ), (4811753259118585472/3328741896069:ℝ), (21368556829353082880/29958677064621:ℝ)],
![(21349152765838332160/29958677064621:ℝ), (4680821016405698816/3328741896069:ℝ), (20779748381812957184/29958677064621:ℝ)]]
theorem admission31_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2536590378639277/5112947552361984:ℝ) admission31_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission31_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_03_coefficients]
def admission31_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(413777155474720916/3328741896069:ℝ), (809926101636122240/3328741896069:ℝ), (396228432082776064/3328741896069:ℝ)],
![(433533389317586696/3328741896069:ℝ), (849008612997138688/3328741896069:ℝ), (415556648281935872/3328741896069:ℝ)]]
theorem admission31_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (96735457051459/1136210567191552:ℝ) admission31_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission31_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_04_coefficients]
def admission31_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8588942529298445232/138697579002875:ℝ), (776297874979971855536/6241391055129375:ℝ), (389723269308964182596/6241391055129375:ℝ)],
![(35418472270773059804/693487895014375:ℝ), (641668227201909061784/6241391055129375:ℝ), (322828024135481748548/6241391055129375:ℝ)]]
theorem admission31_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (26563854203079794853/727174763002593280000:ℝ) admission31_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission31_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_05_coefficients]
def admission31_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9765336333876671699554051020882176/409979336593866524313152157:ℝ), (85879100102838566940397556773077760/1229938009781599572939456471:ℝ), (83889268724768607357454628604362752/1229938009781599572939456471:ℝ), (9102042381061958464149074964643840/409979336593866524313152157:ℝ)],
![(10191888324836031794325982847539712/409979336593866524313152157:ℝ), (89686763650106825418203403364748800/1229938009781599572939456471:ℝ), (87665942960992262581029632084967424/1229938009781599572939456471:ℝ), (3172754730421190431437797473648640/136659778864622174771050719:ℝ)]]
theorem admission31_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (8680384045659979309224200215/69969806778686553482777968128:ℝ) admission31_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission31_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_06_coefficients]
def admission31_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(35242043251807746267050289556988/99724703495805370778874849:ℝ), (69451441914043069489666817734528/99724703495805370778874849:ℝ), (34213249055366453384660596326400/99724703495805370778874849:ℝ)],
![(33008453501318689629280173375896/99724703495805370778874849:ℝ), (65018556882829354027410363425536/99724703495805370778874849:ℝ), (32013825901807181381360986562560/99724703495805370778874849:ℝ)]]
theorem admission31_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3907937732154196945966917305/17019682729950783279594640896:ℝ) admission31_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission31_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_07_coefficients]
def admission31_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(879335946878103921693307264835289109303406679673/1154221105275525124755495937500000000000000:ℝ), (24470446234866963345324737314019811631085189454271/10387989947479726122799463437500000000000000:ℝ), (75599981772108124626065954387443729489258590176951/31163969842439178368398390312500000000000000:ℝ), (25930471707089872930787160760833725472757502165309/31163969842439178368398390312500000000000000:ℝ)],
![(1552286843319068364856736951531652260963626208539/1154221105275525124755495937500000000000000:ℝ), (42421948340879148500753287653570900715952557410673/10387989947479726122799463437500000000000000:ℝ), (25761008017066820964397344019223747245807292720011/6232793968487835673679678062500000000000000:ℝ), (43450692005548114027175758020069382855821698998589/31163969842439178368398390312500000000000000:ℝ)]]
theorem admission31_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (879335946878103921693307264835289109303406679673/206555912479639728335465626992640000000000000000000:ℝ) admission31_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission31_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_08_coefficients]
def admission31_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(28137263984542753890972112818916887973259/19477481151524486480248993945312500:ℝ), (27152290557154960595787199696661247371209/6492493717174828826749664648437500:ℝ), (19627686850306839056007700430311524375392/4869370287881121620062248486328125:ℝ), (251912688732369214440660172473862746112/194774811515244864802489939453125:ℝ)],
![(7900096508699984099405994365252497574479/9738740575762243240124496972656250:ℝ), (7477450603894756759684961227328898588149/3246246858587414413374832324218750:ℝ), (10583626489253870132758751619160552025024/4869370287881121620062248486328125:ℝ), (663506383009822373086663191527831211008/973874057576224324012449697265625:ℝ)]]
theorem admission31_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (647955452158029661217444522976397667/170196827299507832795946408960000000000:ℝ) admission31_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission31_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_09_coefficients]
def admission31_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5372229586347717196799316352/162536225393994140625:ℝ), (138505561561321120979817928768/1462826028545947265625:ℝ), (131972555887049962175129316032/1462826028545947265625:ℝ), (41817261534889545966505234432/1462826028545947265625:ℝ)],
![(23584012450855031431325198848/487608676181982421875:ℝ), (199897075340218366341432118528/1462826028545947265625:ℝ), (187556107903009671799237447424/1462826028545947265625:ℝ), (11682296316196279950356185088/292565205709189453125:ℝ)],
![(1448722853301314994075900416/97521735236396484375:ℝ), (19799944309911033052726289152/487608676181982421875:ℝ), (17871147181721652154414072064/487608676181982421875:ℝ), (5314887422692194072067284992/487608676181982421875:ℝ)]]
theorem admission31_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (648789968590355721687901/908968453753241600000000000:ℝ) admission31_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission31_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_10_coefficients]
def admission31_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(28971982413261850278347754215300/99724703495805370778874849:ℝ), (57105570442728096174928117742080/99724703495805370778874849:ℝ), (28137287785658077597312705822720/99724703495805370778874849:ℝ)],
![(27099919271305254498343167408488/99724703495805370778874849:ℝ), (53390415495415589521588709057536/99724703495805370778874849:ℝ), (26294064433395863338791155580928/99724703495805370778874849:ℝ)]]
theorem admission31_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1604862331139884236986764867/8509841364975391639797320448:ℝ) admission31_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission31_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_11_coefficients]
def admission31_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission31_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission31_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission31_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_12_coefficients]
def admission31_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(90888625094643931/20000000000000000000:ℝ)]]
theorem admission31_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (90888625094643931/20000000000000000000:ℝ) admission31_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission31_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_13_coefficients]
def admission31_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission31_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission31_14_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission31_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_14_coefficients]
theorem admission31_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission31_00_pos hδ hp
 · exact admission31_01_pos hδ hp
 · exact admission31_02_pos hδ hp
 · exact admission31_03_pos hδ hp
 · exact admission31_04_pos hδ hp
 · exact admission31_05_pos hδ hp
 · exact admission31_06_pos hδ hp
 · exact admission31_07_pos hδ hp
 · exact admission31_08_pos hδ hp
 · exact admission31_09_pos hδ hp
 · exact admission31_10_pos hδ hp
 · exact admission31_11_pos hδ hp
 · exact admission31_12_pos hδ hp
 · exact admission31_13_pos hδ hp
 · exact admission31_14_pos hδ hp
#print axioms admission31_all
end
end Record1252270103Return.C30
