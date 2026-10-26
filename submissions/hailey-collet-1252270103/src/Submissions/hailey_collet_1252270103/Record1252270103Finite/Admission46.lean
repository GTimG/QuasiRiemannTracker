/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission46_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(200493046041676823/52468862730263:ℝ), (601121731536839680/157406588190789:ℝ)]]
theorem admission46_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission46_00_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission46_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_00_coefficients]
def admission46_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(146712461743157248/52468862730263:ℝ), (439937385229471744/157406588190789:ℝ)]]
theorem admission46_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission46_01_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission46_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_01_coefficients]
def admission46_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(74643113123470762/52468862730263:ℝ), (74611037739552768/52468862730263:ℝ)]]
theorem admission46_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission46_02_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission46_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_02_coefficients]
def admission46_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21917454288645680115027968/472219764572367:ℝ), (131448683965098017217556480/1416659293717101:ℝ), (9385189372080139553210368/202379899102443:ℝ)],
![(3129726649824755168608256/67459966367481:ℝ), (131392479092427186543689728/1416659293717101:ℝ), (65668223953307328002916352/1416659293717101:ℝ)]]
theorem admission46_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1957065580883840561/3868424311376830464:ℝ) admission46_03_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission46_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_03_coefficients]
def admission46_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(54714989945544436242474/7495551818609:ℝ), (765471772776507091324928/52468862730263:ℝ), (382466923442381984366592/52468862730263:ℝ)],
![(383310751373929388910288/52468862730263:ℝ), (766083201310131250757632/52468862730263:ℝ), (382772530252963192504320/52468862730263:ℝ)]]
theorem admission46_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (136780830660718197/1719299693945257984:ℝ) admission46_04_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission46_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_04_coefficients]
def admission46_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1269744249525779625634071346/295137352857729375:ℝ), (2539597560912552412117422928/295137352857729375:ℝ), (423284364782600612025525944/98379117619243125:ℝ)],
![(1266560878281919462374198232/295137352857729375:ℝ), (2533232109227491393350275152/295137352857729375:ℝ), (84444734254659296402039128/19675823523848625:ℝ)]]
theorem admission46_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (158320109785239932796774779/3380280742271892817182720000:ℝ) admission46_05_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission46_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_05_coefficients]
def admission46_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(354603967851208900714122810139545477000871936/8250685723952923479064059359493:ℝ), (1062981110422723469064704350893386914138243072/8250685723952923479064059359493:ℝ), (1062150577486687040001546572242525116386246656/8250685723952923479064059359493:ℝ), (353773434892628836656878100840283679248875520/8250685723952923479064059359493:ℝ)],
![(354865279289241412968449362796459398901137408/8250685723952923479064059359493:ℝ), (1063764835611126827248905481819633645335740416/8250685723952923479064059359493:ℝ), (1062934093618772557047060279854661017333137408/8250685723952923479064059359493:ℝ), (354034537274334501126494822300286770898534400/8250685723952923479064059359493:ℝ)]]
theorem admission46_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20592324138422778147323877832403155/180238979868326264374647398061244416:ℝ) admission46_06_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission46_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_06_coefficients]
def admission46_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1655953181373359450951842508149873569490/74330502017593905216793327563:ℝ), (3310212032696500550331684490025692393472/74330502017593905216793327563:ℝ), (61268854171785056927370919901480878080/2752981556207181674696049169:ℝ)],
![(33761994751606179721916291413435696240/1516949020767222555444761787:ℝ), (67489428221875512474208962261632712704/1516949020767222555444761787:ℝ), (1249164362248735571233676709844746240/56183297065452687238694881:ℝ)]]
theorem admission46_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (55841998558434944058970065855/230126784780094206929694232576:ℝ) admission46_07_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission46_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_07_coefficients]
def admission46_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(14513752303389267483954144743807573541634591543427078316947/15554653044976403156416014417480468750000000000:ℝ), (61097003297536358777193331599809277329353928010876977157679/21776514262966964418982420184472656250000000000:ℝ), (306181192975919929442545320355956666824153595366785190163697/108882571314834822094912100922363281250000000000:ℝ), (102292442557507736883696172491268245199885392070198446343931/108882571314834822094912100922363281250000000000:ℝ)],
![(4141968142423156754127447347174352385783970709294981317987/4355302852593392883796484036894531250000000000:ℝ), (311341544136651863298332518533146050651413523088625399977249/108882571314834822094912100922363281250000000000:ℝ), (12481417461719967195741622744857946659556522303852217743001/4355302852593392883796484036894531250000000000:ℝ), (104243095912449208386609973402888431226634350409585826547451/108882571314834822094912100922363281250000000000:ℝ)]]
theorem admission46_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (14513752303389267483954144743807573541634591543427078316947/5837660804769423351132363554269264084992000000000000000000000:ℝ) admission46_08_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission46_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_08_coefficients]
def admission46_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7011559349073207808981189939815075362579092213814/2177651426296696441898242018447265625:ℝ), (21007716021105927072000947399685408101672516616176/2177651426296696441898242018447265625:ℝ), (20980757728592504815884969090069463355625578627072/2177651426296696441898242018447265625:ℝ), (199560030213294941790046007562349255437064339456/62218612179905612625664057669921875:ℝ)],
![(6968647780637836944669376849745146591599562747472/2177651426296696441898242018447265625:ℝ), (20879028368837715802008536755239221209826140323968/2177651426296696441898242018447265625:ℝ), (20852117117951113349889710817813420534418404540416/2177651426296696441898242018447265625:ℝ), (1388347306131426736632774359910586377222209142784/435530285259339288379648403689453125:ℝ)]]
theorem admission46_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5171996750427137079211973994637229953789/608915472528129271535970939396096000000000:ℝ) admission46_09_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission46_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_09_coefficients]
def admission46_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1434901562371938164761231705753450496/307434742560134765625:ℝ), (27629600449295487694749965607553755136/1976366202172294921875:ℝ), (193102726161861831761320361206156754944/13834563415206064453125:ℝ), (2380225678926639958616241804155027456/512391237600224609375:ℝ)],
![(128700346958156666147376458257473634304/13834563415206064453125:ℝ), (42832491048441969550292443879450771456/1537173712800673828125:ℝ), (42764873276458328928717077840756998144/1537173712800673828125:ℝ), (128091787025287171428198163909229674496/13834563415206064453125:ℝ)],
![(64129580051129350648959914850262581248/13834563415206064453125:ℝ), (27440660956585615967211290481730912256/1976366202172294921875:ℝ), (38356108787494251696224808138145005568/2766912683041212890625:ℝ), (63825497299995925859604922168871223296/13834563415206064453125:ℝ)]]
theorem admission46_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7430265808943184774788669563/3301055412374895329280000000000:ℝ) admission46_10_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission46_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_10_coefficients]
def admission46_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1358007182553444564958204960565594087726/74330502017593905216793327563:ℝ), (2714628859031964726794639627101621673984/74330502017593905216793327563:ℝ), (1356621878872454433781708267504585932800/74330502017593905216793327563:ℝ)],
![(193807023367539801483918971644819349744/10618643145370557888113332509:ℝ), (387416218572361452034295876482805989376/10618643145370557888113332509:ℝ), (193609224102992296079717082105097748480/10618643145370557888113332509:ℝ)]]
theorem admission46_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5770004513948926212779196563515/28995974882291870073141473304576:ℝ) admission46_11_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission46_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_11_coefficients]
def admission46_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission46_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission46_12_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission46_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_12_coefficients]
def admission46_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission46_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission46_13_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission46_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_13_coefficients]
def admission46_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission46_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission46_14_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission46_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_14_coefficients]
theorem admission46_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission46_00_pos hδ hp
 · exact admission46_01_pos hδ hp
 · exact admission46_02_pos hδ hp
 · exact admission46_03_pos hδ hp
 · exact admission46_04_pos hδ hp
 · exact admission46_05_pos hδ hp
 · exact admission46_06_pos hδ hp
 · exact admission46_07_pos hδ hp
 · exact admission46_08_pos hδ hp
 · exact admission46_09_pos hδ hp
 · exact admission46_10_pos hδ hp
 · exact admission46_11_pos hδ hp
 · exact admission46_12_pos hδ hp
 · exact admission46_13_pos hδ hp
 · exact admission46_14_pos hδ hp
#print axioms admission46_all
end
end Record1252270103Finite
