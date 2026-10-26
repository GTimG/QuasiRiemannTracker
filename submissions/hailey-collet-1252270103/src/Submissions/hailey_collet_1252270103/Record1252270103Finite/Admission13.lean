/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission13_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1806072133773489/7495551818609:ℝ), (37570108221052480/157406588190789:ℝ)]]
theorem admission13_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission13_00_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission13_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_00_coefficients]
def admission13_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1318861265563904/7495551818609:ℝ), (27496086576841984/157406588190789:ℝ)]]
theorem admission13_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission13_01_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission13_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_01_coefficients]
def admission13_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(670752177520006/7495551818609:ℝ), (4663189858722048/52468862730263:ℝ)]]
theorem admission13_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission13_02_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission13_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_02_coefficients]
def admission13_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(87585933722225203200/7495551818609:ℝ), (4698231759846755928064/202379899102443:ℝ), (16334154445426728091648/1416659293717101:ℝ)],
![(1827097007007798787328/157406588190789:ℝ), (32667980033287351280896/1416659293717101:ℝ), (16224382370217162194944/1416659293717101:ℝ)]]
theorem admission13_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (990257713025949841/1934212155688415232:ℝ) admission13_03_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission13_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_03_coefficients]
def admission13_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(92773565736211694832/52468862730263:ℝ), (183495712169152325632/52468862730263:ℝ), (90727021891296165888/52468862730263:ℝ)],
![(93980806444287404442/52468862730263:ℝ), (26556671057953851648/7495551818609:ℝ), (13131542642161287168/7495551818609:ℝ)]]
theorem admission13_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1038288366981081/13432028858947328:ℝ) admission13_04_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission13_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_04_coefficients]
def admission13_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(343415510154889801008973/295137352857729375:ℝ), (137384751988317057241394/59027470571545875:ℝ), (114498356544481866775999/98379117619243125:ℝ)],
![(330904757053932571477699/295137352857729375:ℝ), (661983091490004821774794/295137352857729375:ℝ), (22071004504752521780723/19675823523848625:ℝ)]]
theorem admission13_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (330904757053932571477699/6602110824749790658560000:ℝ) admission13_05_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission13_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_05_coefficients]
def admission13_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5456797453083660565591410828702875459584/8250685723952923479064059359493:ℝ), (16169313729775386625898464820244714692608/8250685723952923479064059359493:ℝ), (15969236095745832415790781721213682581504/8250685723952923479064059359493:ℝ), (5256718450043910949485542129671843348480/8250685723952923479064059359493:ℝ)],
![(5521363850427055409861284390906341354496/8250685723952923479064059359493:ℝ), (16362187870775149882782461108334947986432/8250685723952923479064059359493:ℝ), (16161289547067456340465307134796517277696/8250685723952923479064059359493:ℝ), (5320464148702520439138062017367910645760/8250685723952923479064059359493:ℝ)]]
theorem admission13_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (156662417949554650470183555176015/1408117030221298940426932797353472:ℝ) admission13_06_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission13_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_06_coefficients]
def admission13_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(427681977809202066944985701619440080/74330502017593905216793327563:ℝ), (848490420225892314849914376719833088/74330502017593905216793327563:ℝ), (15586003979603675833731359380439040/2752981556207181674696049169:ℝ)],
![(60189015395814973938309907526948770/10618643145370557888113332509:ℝ), (17057644441789117983120947035298048/1516949020767222555444761787:ℝ), (2193201226105762877519233751285760/393283079458168810670864167:ℝ)]]
theorem admission13_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (200793569284585224382254066585/805443746730329724253929814016:ℝ) admission13_07_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission13_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_07_coefficients]
def admission13_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(787949972120497844338014655897071103647155900030884417/217765142629669644189824201844726562500000000000:ℝ), (556840001497733456824530555199182599821560489620223731/43553028525933928837964840368945312500000000000:ℝ), (3203921926107325679523379318312736147741213779682538301/217765142629669644189824201844726562500000000000:ℝ), (1207665276914784521521827903089991032954146919112304063/217765142629669644189824201844726562500000000000:ℝ)],
![(7033319159855195442354957672996279640000104111504528031/871060570518678576759296807378906250000000000000:ℝ), (22709418240483609673124877973084656214866884953208443927/871060570518678576759296807378906250000000000000:ℝ), (6079164162875777625227935580502005401866345810879777277/217765142629669644189824201844726562500000000000:ℝ), (308590390768899986257708179209576427332523104752328329/31109306089952806312832028834960937500000000000:ℝ)]]
theorem admission13_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (787949972120497844338014655897071103647155900030884417/1247058887737608748105668483883204608000000000000000000000:ℝ) admission13_08_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission13_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_08_coefficients]
def admission13_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(142114795181541498206261667182488453735272776/2177651426296696441898242018447265625:ℝ), (418913108318759473172670974197967328034414424/2177651426296696441898242018447265625:ℝ), (411499425599801661150451868504750604117014528/2177651426296696441898242018447265625:ℝ), (26940233490653875673292127274297431244824576/435530285259339288379648403689453125:ℝ)],
![(131465397545251761355186822586771971936290779/2177651426296696441898242018447265625:ℝ), (387150054529222096571934094902208854177497441/2177651426296696441898242018447265625:ℝ), (379920796719492608666100934598856390021431552/2177651426296696441898242018447265625:ℝ), (24847239017597758510804897531656217661513728/435530285259339288379648403689453125:ℝ)]]
theorem admission13_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3033110231640351380713488468219753132509/304457736264064635767985469698048000000000:ℝ) admission13_09_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission13_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_09_coefficients]
def admission13_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83753324921530856482924626337792/13834563415206064453125:ℝ), (246185478912792421782693020622848/13834563415206064453125:ℝ), (48223997434825981090282176446464/2766912683041212890625:ℝ), (78687860799368340151642487947264/13834563415206064453125:ℝ)],
![(32224569614888727207761982900224/2766912683041212890625:ℝ), (67615609642662156925721347831808/1976366202172294921875:ℝ), (463267657171363370230034086141952/13834563415206064453125:ℝ), (151081293343546907788794565820416/13834563415206064453125:ℝ)],
![(8591196455863445993521236361088/1537173712800673828125:ℝ), (25219814811406050064145322442112/1537173712800673828125:ℝ), (4933400487615273890769033160192/307434742560134765625:ℝ), (8038387191541577883221079719936/1537173712800673828125:ℝ)]]
theorem admission13_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (735936327350608326710914281/275087951031241277440000000000:ℝ) admission13_10_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission13_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_10_coefficients]
def admission13_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(351075853905225239780900185219175984/74330502017593905216793327563:ℝ), (696518349617721690007155813437075456/74330502017593905216793327563:ℝ), (345455618991043448828203627091640320/74330502017593905216793327563:ℝ)],
![(49389922747861065308437427685578078/10618643145370557888113332509:ℝ), (97981438415421087321091966381286912/10618643145370557888113332509:ℝ), (48593375173101987542595667280445440/10618643145370557888113332509:ℝ)]]
theorem admission13_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2965904246405150606847880083035/14497987441145935036570736652288:ℝ) admission13_11_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission13_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_11_coefficients]
def admission13_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission13_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission13_12_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission13_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_12_coefficients]
def admission13_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission13_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission13_13_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission13_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_13_coefficients]
def admission13_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission13_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission13_14_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission13_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_14_coefficients]
theorem admission13_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission13_00_pos hδ hp
 · exact admission13_01_pos hδ hp
 · exact admission13_02_pos hδ hp
 · exact admission13_03_pos hδ hp
 · exact admission13_04_pos hδ hp
 · exact admission13_05_pos hδ hp
 · exact admission13_06_pos hδ hp
 · exact admission13_07_pos hδ hp
 · exact admission13_08_pos hδ hp
 · exact admission13_09_pos hδ hp
 · exact admission13_10_pos hδ hp
 · exact admission13_11_pos hδ hp
 · exact admission13_12_pos hδ hp
 · exact admission13_13_pos hδ hp
 · exact admission13_14_pos hδ hp
#print axioms admission13_all
end
end Record1252270103Finite
