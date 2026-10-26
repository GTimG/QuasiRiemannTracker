/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19142460698717029/157406588190789:ℝ), (18785054110526240/157406588190789:ℝ)]]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission16_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission16_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]
def admission16_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13948043288420992/157406588190789:ℝ), (13748043288420992/157406588190789:ℝ)]]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission16_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission16_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]
def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363670313279018/52468862730263:ℝ), (2331594929361024/52468862730263:ℝ)]]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission16_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission16_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]
def admission16_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2089826440385797760128/1416659293717101:ℝ), (458288487929282322560/157406588190789:ℝ), (290701221568249020416/202379899102443:ℝ)],
![(2062336153973002074880/1416659293717101:ℝ), (452184587349817082624/157406588190789:ℝ), (2007465532175351668736/1416659293717101:ℝ)]]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (245051944845623983/483553038922103808:ℝ) admission16_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission16_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]
def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1715671818217469134/7495551818609:ℝ), (3356761819264532096/7495551818609:ℝ), (1641442830270160896/7495551818609:ℝ)],
![(1759270709756269524/7495551818609:ℝ), (24100937051197620480/52468862730263:ℝ), (11788543962849337344/52468862730263:ℝ)]]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (601114317725889/7675445062255616:ℝ) admission16_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission16_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]
def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(668863439904530558956/4684719886630625:ℝ), (12049581999892678563164/42162478979675625:ℝ), (1205771442774395530762/8432495795935125:ℝ)],
![(618896465448872769758/4684719886630625:ℝ), (78091740804537404534636/295137352857729375:ℝ), (39094499981564400172382/295137352857729375:ℝ)]]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (928344698173309154637/19649139359374376960000:ℝ) admission16_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission16_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]
def admission16_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(357870274113898161638749833948524473856/8250685723952923479064059359493:ℝ), (349338927076060266990014280089313524224/2750228574650974493021353119831:ℝ), (1022676209919933892184397482404910514176/8250685723952923479064059359493:ℝ), (332529009293907527446128876085494415360/8250685723952923479064059359493:ℝ)],
![(366044751455491172428691619540573983744/8250685723952923479064059359493:ℝ), (357443921021409675231491078469221702656/2750228574650974493021353119831:ℝ), (1046784935753361314733333877914593951744/8250685723952923479064059359493:ℝ), (340497221626233713652693862047502827520/8250685723952923479064059359493:ℝ)]]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (634248751247229628460176231547345/5632468120885195761707731189413888:ℝ) admission16_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission16_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]
def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5989000699744333242423279037292374/8258944668621545024088147507:ℝ), (106102848155931805698458016110870144/74330502017593905216793327563:ℝ), (1933650785146500998522874727464960/2752981556207181674696049169:ℝ)],
![(5810920957720777858731585258915076/8258944668621545024088147507:ℝ), (102923464724474070689769792255178496/74330502017593905216793327563:ℝ), (1875251935930667075748693947105280/2752981556207181674696049169:ℝ)]]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (343368884752929762405156362385/1409526556778077017444377174528:ℝ) admission16_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission16_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]
def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1183599013228794597533439281201220999036108907227229/2633592049943094714313822546875000000000000000:ℝ), (260397946040070740937679083312207896390825230251095581/165916299146414967001770820453125000000000000000:ℝ), (6237157650595421059010547328453879628646577489200936227/3484242282074714307037187229515625000000000000000:ℝ), (2334648671468617877887361092711934671623560363189552993/3484242282074714307037187229515625000000000000000:ℝ)],
![(2677835365892220300479039285307767910999880804730623/2633592049943094714313822546875000000000000000:ℝ), (539355244978897302905529547547927808491367275820333307/165916299146414967001770820453125000000000000000:ℝ), (12023321846864136548135996268948692894906016729065926691/3484242282074714307037187229515625000000000000000:ℝ), (4239583588403648642451619795466022588370589991497541473/3484242282074714307037187229515625000000000000000:ℝ)]]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1183599013228794597533439281201220999036108907227229/942599310459265871584027576631296000000000000000000000:ℝ) admission16_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission16_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]
def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(17948820977067137561084105876662604143957817/4355302852593392883796484036894531250:ℝ), (5785907991859609882479396468036183116339789/483922539177043653755164892988281250:ℝ), (25153940197125320518418603360007912268946752/2177651426296696441898242018447265625:ℝ), (231194073697551938321861717883721646903296/62218612179905612625664057669921875:ℝ)],
![(7620004072595330335302433103171262167128939/2177651426296696441898242018447265625:ℝ), (2446667652419318081477861738197602074906023/241961269588521826877582446494140625:ℝ), (21183647614028277076994425650986634213758848/2177651426296696441898242018447265625:ℝ), (1356734206750848922942128307355899830409216/435530285259339288379648403689453125:ℝ)]]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (662467874390062950655336087576122964067/76114434066016158941996367424512000000000:ℝ) admission16_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission16_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]
def admission16_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(178108458743462550149437217728/922304227680404296875:ℝ), (856456452168286316378906087872/1537173712800673828125:ℝ), (7402363602693536635886269783936/13834563415206064453125:ℝ), (2365889501338710540717673259008/13834563415206064453125:ℝ)],
![(547360632141921858560801614592/1537173712800673828125:ℝ), (225030150155514028620040553216/219596244685810546875:ℝ), (13577029694078305703254446111232/13834563415206064453125:ℝ), (618055754521709803891300827136/1976366202172294921875:ℝ)],
![(149894857565281122210124572416/922304227680404296875:ℝ), (716711927038625137175068294912/1537173712800673828125:ℝ), (2052161503454123883974961183232/4611521138402021484375:ℝ), (651502434258404083500379160576/4611521138402021484375:ℝ)]]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (39764552872217046112083689/17192996939452579840000000000:ℝ) admission16_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission16_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]
def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(14745554352681263082742434447548542/24776834005864635072264442521:ℝ), (29026928661231954980420577938260736/24776834005864635072264442521:ℝ), (42850577825172335101648331128422400/74330502017593905216793327563:ℝ)],
![(14296303515966887332878882424806388/24776834005864635072264442521:ℝ), (28135880672824531192174229165003264/24776834005864635072264442521:ℝ), (41525079630339951094139842096291840/74330502017593905216793327563:ℝ)]]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5068979447062982311296367443395/25371478022005386313998789141504:ℝ) admission16_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission16_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]
def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission16_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission16_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]
def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission16_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission16_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]
def admission16_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission16_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission16_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]
theorem admission16_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission16_00_pos hδ hp
 · exact admission16_01_pos hδ hp
 · exact admission16_02_pos hδ hp
 · exact admission16_03_pos hδ hp
 · exact admission16_04_pos hδ hp
 · exact admission16_05_pos hδ hp
 · exact admission16_06_pos hδ hp
 · exact admission16_07_pos hδ hp
 · exact admission16_08_pos hδ hp
 · exact admission16_09_pos hδ hp
 · exact admission16_10_pos hδ hp
 · exact admission16_11_pos hδ hp
 · exact admission16_12_pos hδ hp
 · exact admission16_13_pos hδ hp
 · exact admission16_14_pos hδ hp
#print axioms admission16_all
end
end Record1252270103Finite
