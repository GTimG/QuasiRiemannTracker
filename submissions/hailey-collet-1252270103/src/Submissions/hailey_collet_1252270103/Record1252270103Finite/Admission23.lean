/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission23_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1806072133773489/7495551818609:ℝ), (37570108221052480/157406588190789:ℝ)]]
theorem admission23_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission23_00_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission23_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_00_coefficients]
def admission23_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1318861265563904/7495551818609:ℝ), (27496086576841984/157406588190789:ℝ)]]
theorem admission23_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission23_01_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission23_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_01_coefficients]
def admission23_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(670752177520006/7495551818609:ℝ), (4663189858722048/52468862730263:ℝ)]]
theorem admission23_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission23_02_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission23_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_02_coefficients]
def admission23_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3593091784740406227200/157406588190789:ℝ), (64237159827050150951168/1416659293717101:ℝ), (31899904364386494906368/1416659293717101:ℝ)],
![(3580884183581475747328/157406588190789:ℝ), (64017517541410210735616/1416659293717101:ℝ), (4541447469882418429952/202379899102443:ℝ)]]
theorem admission23_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (138593977962720289/276316022241202176:ℝ) admission23_03_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission23_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_03_coefficients]
def admission23_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(193481712752494126722/52468862730263:ℝ), (382685136563297942272/52468862730263:ℝ), (189213591707505819648/52468862730263:ℝ)],
![(194688953460569836332/52468862730263:ℝ), (385086121799822578176/52468862730263:ℝ), (190407368311338663936/52468862730263:ℝ)]]
theorem admission23_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (17323021701736983/214912461743157248:ℝ) admission23_04_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission23_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_04_coefficients]
def admission23_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(599255748603078995299028/295137352857729375:ℝ), (34278510492117465404884/8432495795935125:ℝ), (28593553860218262896222/14054159659891875:ℝ)],
![(586744995502121765767754/295137352857729375:ℝ), (1174807198772530824738764/295137352857729375:ℝ), (39202308600161716480234/19675823523848625:ℝ)]]
theorem admission23_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (293372497751060882883877/6602110824749790658560000:ℝ) admission23_05_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission23_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_05_coefficients]
def admission23_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(11338611030350492423949798696026370120704/8250685723952923479064059359493:ℝ), (33602950168704810543064743575589149907968/8250685723952923479064059359493:ℝ), (33192125934829890804126256008930903916544/8250685723952923479064059359493:ℝ), (10927783941368783581712463529368124129280/8250685723952923479064059359493:ℝ)],
![(11403177427693887268219672258229836015616/8250685723952923479064059359493:ℝ), (33795824309704573799948739863679383201792/8250685723952923479064059359493:ℝ), (33384179386151514728800781422513738612736/8250685723952923479064059359493:ℝ), (10991529640027393071364983417064191426560/8250685723952923479064059359493:ℝ)]]
theorem admission23_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2605386720030017753055683023778945/22529872483540783046830924757655552:ℝ) admission23_06_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission23_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_06_coefficients]
def admission23_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(810541099409800273949028012811569830/74330502017593905216793327563:ℝ), (1608009795518573455814323408912837888/74330502017593905216793327563:ℝ), (29536840181164001829785656910807040/2752981556207181674696049169:ℝ)],
![(804182229371303024572211663880771140/74330502017593905216793327563:ℝ), (227906278991478274591047919560372736/10618643145370557888113332509:ℝ), (29303244784300666138688933789368320/2752981556207181674696049169:ℝ)]]
theorem admission23_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1341396093031341528565472432985/5638106227112308069777508698112:ℝ) admission23_07_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission23_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_07_coefficients]
def admission23_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(63066950081779618354445922136657075588703741048447025391/1742121141037357153518593614757812500000000000000:ℝ), (38811204402003234392668064017129780774800930681332495261/348424228207471430703718722951562500000000000000:ℝ), (198908691858081254690534857433775967001825411775574842163/1742121141037357153518593614757812500000000000000:ℝ), (67919509583406499256653011350348490267762644729859391249/1742121141037357153518593614757812500000000000000:ℝ)],
![(70829988624526026484451720235473066039526702071209006117/1742121141037357153518593614757812500000000000000:ℝ), (217201258431074053036608853823850912310876003728270414919/1742121141037357153518593614757812500000000000000:ℝ), (221910629752228870256171307531290121034826468025152753971/1742121141037357153518593614757812500000000000000:ℝ), (75539249251146622314910046161364841934750763243091345169/1742121141037357153518593614757812500000000000000:ℝ)]]
theorem admission23_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (63066950081779618354445922136657075588703741048447025391/19952942203801739969690695742131273728000000000000000000000:ℝ) admission23_08_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission23_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_08_coefficients]
def admission23_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(208577255282999932223167246899899051583105031/2177651426296696441898242018447265625:ℝ), (613276019948583595159613194388783718426884389/2177651426296696441898242018447265625:ℝ), (600846178330636184628192273070585647489426688/2177651426296696441898242018447265625:ℝ), (39229505669914931209173646350106367406473216/435530285259339288379648403689453125:ℝ)],
![(197927857646710195372092402304182569784123034/2177651426296696441898242018447265625:ℝ), (581512966159046218558876315093025244569967406/2177651426296696441898242018447265625:ℝ), (569267549450327132143841339164691433393843712/2177651426296696441898242018447265625:ℝ), (5305215885265544863812345229637879117594624/62218612179905612625664057669921875:ℝ)]]
theorem admission23_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (323804680497164603504171461769890082861/43493962323437805109712209956864000000000:ℝ) admission23_09_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission23_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_09_coefficients]
def admission23_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(240930980039591509267334037114752/13834563415206064453125:ℝ), (704964413726155517336236306238848/13834563415206064453125:ℝ), (137432514062680794547350834226688/2766912683041212890625:ℝ), (223129256742597777167851902009344/13834563415206064453125:ℝ)],
![(93565345047652191742308242825728/2766912683041212890625:ℝ), (1368023609435517665380538081890816/13834563415206064453125:ℝ), (190374236693545061726214068770816/1976366202172294921875:ℝ), (432423013646902475414501613633536/13834563415206064453125:ℝ)],
![(75615663382842561276671005366784/4611521138402021484375:ℝ), (31567320972674948663059679211008/658788734057431640625:ℝ), (43020829232457687976848506570752/922304227680404296875:ℝ), (69748603028000110519495783743488/4611521138402021484375:ℝ)]]
theorem admission23_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (532139610504151233821836729/275087951031241277440000000000:ℝ) admission23_10_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission23_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_10_coefficients]
def admission23_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(664460533773856521658107618747802714/74330502017593905216793327563:ℝ), (1318232963360334788501062466431545856/74330502017593905216793327563:ℝ), (653797288526780145446169561283624960/74330502017593905216793327563:ℝ)],
![(659114139103658739036269427327673276/74330502017593905216793327563:ℝ), (186797811807222958534507202523354112/10618643145370557888113332509:ℝ), (648495295747450609416135605155102720/74330502017593905216793327563:ℝ)]]
theorem admission23_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (19790505851667804242435778965915/101485912088021545255995156566016:ℝ) admission23_11_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission23_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_11_coefficients]
def admission23_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission23_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission23_12_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission23_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_12_coefficients]
def admission23_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission23_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission23_13_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission23_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_13_coefficients]
def admission23_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission23_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission23_14_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_14_coefficients,Fin.sum_univ_succ] <;> ring
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
end Record1252270103Finite
