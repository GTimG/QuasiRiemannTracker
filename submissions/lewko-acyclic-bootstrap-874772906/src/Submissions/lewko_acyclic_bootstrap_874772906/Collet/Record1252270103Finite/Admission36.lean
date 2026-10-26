/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission36_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(75497623030295749/157406588190789:ℝ), (75140216442104960/157406588190789:ℝ)]]
theorem admission36_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission36_00_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission36_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_00_coefficients]
def admission36_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(55192173153683968/157406588190789:ℝ), (54992173153683968/157406588190789:ℝ)]]
theorem admission36_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission36_01_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission36_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_01_coefficients]
def admission36_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9358455101362090/52468862730263:ℝ), (9326379717444096/52468862730263:ℝ)]]
theorem admission36_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission36_02_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission36_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_02_coefficients]
def admission36_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129573583358404045090816/1416659293717101:ℝ), (86090119989348561227776/472219764572367:ℝ), (18385334029948805513216/202379899102443:ℝ)],
![(18447757226732023522816/202379899102443:ℝ), (85797329031975846555136/472219764572367:ℝ), (128258249908803375005696/1416659293717101:ℝ)]]
theorem admission36_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1957065580883840561/3868424311376830464:ℝ) admission36_03_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission36_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_03_coefficients]
def admission36_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(107615456331351483216/7495551818609:ℝ), (1498214787591372804096/52468862730263:ℝ), (744916600791694835712/52468862730263:ℝ)],
![(758110196867893572314/52468862730263:ℝ), (1507791864479753453056/52468862730263:ℝ), (749691707207026212864/52468862730263:ℝ)]]
theorem admission36_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131223490119061/26864057717894656:ℝ) admission36_04_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission36_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_04_coefficients]
def admission36_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(840956128431405612307543/98379117619243125:ℝ), (5047347025123448165747306/295137352857729375:ℝ), (2524451585830455249354677/295137352857729375:ℝ)],
![(824328987226507123114009/98379117619243125:ℝ), (4947745679971656142414346/295137352857729375:ℝ), (2474731577581824154886069/295137352857729375:ℝ)]]
theorem admission36_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (824328987226507123114009/17605628865999441756160000:ℝ) admission36_05_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission36_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_05_coefficients]
def admission36_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(87770186606809209568499083805972888109056/8250685723952923479064059359493:ℝ), (87227889416090019806718139280477884104704/2750228574650974493021353119831:ℝ), (260060842009312487703564078116484411293696/8250685723952923479064059359493:ℝ), (86147357557778078860649310481023647088640/8250685723952923479064059359493:ℝ)],
![(88283426295132601083979998957545489291264/8250685723952923479064059359493:ℝ), (87740034842502579523511877132707287156736/2750228574650974493021353119831:ℝ), (261594004198502297278092418423168557645824/8250685723952923479064059359493:ℝ), (86657323147046954777869469582592185466880/8250685723952923479064059359493:ℝ)]]
theorem admission36_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320923915348120327519809121195315/2816234060442597880853865594706944:ℝ) admission36_06_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission36_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_06_coefficients]
def admission36_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1093211254775621792046176047175702576/24776834005864635072264442521:ℝ), (6532656756385114446015377484095123456/74330502017593905216793327563:ℝ), (120483314693289364230109858857615360/2752981556207181674696049169:ℝ)],
![(22138108680236955982483757117872346/505649673589074185148253929:ℝ), (132287689150355573959652151897944576/1516949020767222555444761787:ℝ), (2439774145017061662565774823915520/56183297065452687238694881:ℝ)]]
theorem admission36_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (55841998558434944058970065855/230126784780094206929694232576:ℝ) admission36_07_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission36_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_07_coefficients]
def admission36_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(39728671271994067017454938512563079723517909436299659/192032753641683989585382894042968750000000000:ℝ), (22990246696899622020734609980573998722856979179887114977/36294190438278274031637366974121093750000000000:ℝ), (14072462863874545344918412500623432586434643875244171029/21776514262966964418982420184472656250000000000:ℝ), (23917724052022115161009929579338637557528241955691416867/108882571314834822094912100922363281250000000000:ℝ)],
![(1302310056497599394473824132504693715553820865781760159/5376917101967151708390721033203125000000000000:ℝ), (107295708656360734979490529650009223475400886446291730573/145176761753113096126549467896484375000000000000:ℝ), (81827603543714722909693951135757965190664572323539298537/108882571314834822094912100922363281250000000000:ℝ), (27727593885892176690138446984846813391022301212307393827/108882571314834822094912100922363281250000000000:ℝ)]]
theorem admission36_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (119186013815982201052364815537689239170553728308898977/52785561385718888808705544291352576000000000000000000000:ℝ) admission36_08_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission36_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_08_coefficients]
def admission36_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1831827797963266410551112004398555084540878368/2177651426296696441898242018447265625:ℝ), (362805057857353140428567192082825868799324944/145176761753113096126549467896484375:ℝ), (5388727631123621660750206551406608916257759232/2177651426296696441898242018447265625:ℝ), (50813704974348827560447680807667887274000384/62218612179905612625664057669921875:ℝ)],
![(1747371745291849658802513197887979846872842172/2177651426296696441898242018447265625:ℝ), (69192605474244035045533513263307437605258438/29035352350622619225309893579296875:ℝ), (5136833447219018421063569031224559244876776448/2177651426296696441898242018447265625:ℝ), (338951979035992855623235927712545502251515904/435530285259339288379648403689453125:ℝ)]]
theorem admission36_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5171996750427137079211973994637229953789/608915472528129271535970939396096000000000:ℝ) admission36_09_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission36_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_09_coefficients]
def admission36_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2130091120409641853594697811410944/13834563415206064453125:ℝ), (60144308329672484828103348109312/131757746811486328125:ℝ), (693343610412611279197809145413632/1537173712800673828125:ℝ), (2055031355864032459424128568655872/13834563415206064453125:ℝ)],
![(4152568866433087666927339633168384/13834563415206064453125:ℝ), (4102743758714592886560653930688512/4611521138402021484375:ℝ), (2431775342979577123057250120925184/2766912683041212890625:ℝ), (1334404846215356540843876148576256/4611521138402021484375:ℝ)],
![(2022090939815265315216220076528384/13834563415206064453125:ℝ), (19021973688323112830431657799936/43919248937162109375:ℝ), (5917630255122547143471953124374528/13834563415206064453125:ℝ), (1947799600219602229602200993923072/13834563415206064453125:ℝ)]]
theorem admission36_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7430265808943184774788669563/3301055412374895329280000000000:ℝ) admission36_10_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission36_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_10_coefficients]
def admission36_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(896651399554727694120640355587114960/24776834005864635072264442521:ℝ), (1786045962641843648793974555226087424/24776834005864635072264442521:ℝ), (2668209081900415942085017806419722240/74330502017593905216793327563:ℝ)],
![(127078930024041984997644612878315530/3539547715123519296037777503:ℝ), (253125397875650697368703035410859008/3539547715123519296037777503:ℝ), (378143015826156828280697425986519040/10618643145370557888113332509:ℝ)]]
theorem admission36_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5770004513948926212779196563515/28995974882291870073141473304576:ℝ) admission36_11_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission36_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_11_coefficients]
def admission36_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission36_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission36_12_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission36_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_12_coefficients]
def admission36_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission36_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission36_13_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission36_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_13_coefficients]
def admission36_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission36_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission36_14_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission36_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_14_coefficients]
theorem admission36_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission36_00_pos hδ hp
 · exact admission36_01_pos hδ hp
 · exact admission36_02_pos hδ hp
 · exact admission36_03_pos hδ hp
 · exact admission36_04_pos hδ hp
 · exact admission36_05_pos hδ hp
 · exact admission36_06_pos hδ hp
 · exact admission36_07_pos hδ hp
 · exact admission36_08_pos hδ hp
 · exact admission36_09_pos hδ hp
 · exact admission36_10_pos hδ hp
 · exact admission36_11_pos hδ hp
 · exact admission36_12_pos hδ hp
 · exact admission36_13_pos hδ hp
 · exact admission36_14_pos hδ hp
#print axioms admission36_all
end
end Record1252270103Finite
