/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission30_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10255154572695363/163643883613523:ℝ),(9891510689081840/163643883613523:ℝ)]]
theorem admission30_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618219418067615/654575534454092:ℝ) admission30_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission30_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_00_coefficients]
def admission30_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7473208551265472/163643883613523:ℝ),(7273208551265472/163643883613523:ℝ)]]
theorem admission30_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113643883613523/163643883613523:ℝ) admission30_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission30_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_01_coefficients]
def admission30_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3785518809264106/163643883613523:ℝ),(3688779778172864/163643883613523:ℝ)]]
theorem admission30_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57637184033951/163643883613523:ℝ) admission30_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission30_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_02_coefficients]
def admission30_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(91717767162383890496/490931650840569:ℝ),(536122735546076481728/1472794952521707:ℝ),(261043234058924810240/1472794952521707:ℝ)],
![(89309502725273230976/490931650840569:ℝ),(521690490046451135360/1472794952521707:ℝ),(253837581870631442432/1472794952521707:ℝ)]]
theorem admission30_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123944131772769259/251357005230371328:ℝ) admission30_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission30_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_03_coefficients]
def admission30_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5273046919839422842/163643883613523:ℝ),(10108759688527479488/163643883613523:ℝ),(4839679068962797568/163643883613523:ℝ)],
![(5519698773224842852/163643883613523:ℝ),(10591396708684871552/163643883613523:ℝ),(5075760974765860864/163643883613523:ℝ)]]
theorem admission30_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (7089373636175973/83785668410123776:ℝ) admission30_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission30_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_04_coefficients]
def admission30_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(941783966267930375224/61366456355071125:ℝ),(9499393598106054406016/306832281775355625:ℝ),(1595626388750421100382/102277427258451875:ℝ)],
![(774061360894153644718/61366456355071125:ℝ),(7843070403986699690732/306832281775355625:ℝ),(1323027108605832053214/102277427258451875:ℝ)]]
theorem admission30_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (387030680447076822359/10724565556495843328000:ℝ) admission30_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission30_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_05_coefficients]
def admission30_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9366590188241644878719963641209952000/2972504591496905019399160339719:ℝ),(80600518368529730899440629500931716352/8917513774490715058197481019157:ℝ),(76972175785337992445697214763798720512/8917513774490715058197481019157:ℝ),(24471052264672646690452876186496860160/8917513774490715058197481019157:ℝ)],
![(9757067113464559428930598848462476800/2972504591496905019399160339719:ℝ),(84057021265651160235065231293384385024/8917513774490715058197481019157:ℝ),(80372058390038621290941052458359087104/8917513774490715058197481019157:ℝ),(25585853584094722789924417710362132480/8917513774490715058197481019157:ℝ)]]
theorem admission30_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (373398624644052836463209170326185/3043844701692830739864740187872256:ℝ) admission30_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission30_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_06_coefficients]
def admission30_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21688269139513617520240489490586370/241013885797046352924256243761:ℝ),(42111794329637497587052446921083584/241013885797046352924256243761:ℝ),(20433058579060860814361819386265600/241013885797046352924256243761:ℝ)],
![(20333029414144616123940130982032180/241013885797046352924256243761:ℝ),(39443317445484393824270389640288128/241013885797046352924256243761:ℝ),(19119504813264091190581416711434240/241013885797046352924256243761:ℝ)]]
theorem admission30_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4667847854800803513325541189315/20566518254681288782869866134272:ℝ) admission30_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission30_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_07_coefficients]
def admission30_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(126025844617544093948751458233400159132383371610966961/1506336786231539705776601523506250000000000000000:ℝ),(2024247947264916458023546613277009420477244520921871371/7531683931157698528883007617531250000000000000000:ℝ),(2158550943374298823164156496980282516384214937900524321/7531683931157698528883007617531250000000000000000:ℝ),(50958213732126753062129412463150342589676235002232517/502112262077179901925533841168750000000000000000:ℝ)],
![(47892430197863425615666691226967338484422914329681063/301267357246307941155320304701250000000000000000:ℝ),(3685683754210447983764859057292817061321260150758527077/7531683931157698528883007617531250000000000000000:ℝ),(3780496875776403215725354802321705609068398403386880417/7531683931157698528883007617531250000000000000000:ℝ),(86137561596708473382824052944811650064664907391358661/502112262077179901925533841168750000000000000000:ℝ)]]
theorem admission30_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (126025844617544093948751458233400159132383371610966961/33696183508469823541853988674391244800000000000000000000:ℝ) admission30_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission30_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_08_coefficients]
def admission30_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(15002319847134489637056291715957579968317/75316839311576985288830076175312500:ℝ),(585302681156021237028492324452762854064761/1046067212660791462344862169101562500:ℝ),(1227919212079898514214800743703076315402256/2353651228486780790275939880478515625:ℝ),(5064352515331875389066049153799031643136/31382016379823743870345865073046875:ℝ)],
![(110822125922077196836416181004207469418033/941460491394712316110375952191406250:ℝ),(167657885098581730706556939577634121708261/523033606330395731172431084550781250:ℝ),(678089232457172826425030487167388072097952/2353651228486780790275939880478515625:ℝ),(13380014183558257516897103345122262676224/156910081899118719351729325365234375:ℝ)]]
theorem admission30_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52265680404524443425379309941883838579/13711012169787525855246577422848000000000:ℝ) admission30_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission30_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_09_coefficients]
def admission30_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67077447871727073188792719808/14382763208219794921875:ℝ),(37033270298304834117891161696/2876552641643958984375:ℝ),(169159093239416432374335957536/14382763208219794921875:ℝ),(17024066313310611657890956288/4794254402739931640625:ℝ)],
![(101593602162817628622234135296/14382763208219794921875:ℝ),(274466955991710917094428121472/14382763208219794921875:ℝ),(244244633806170205298763837056/14382763208219794921875:ℝ),(4758359775568461121771323392/958850880547986328125:ℝ)],
![(11223488822736672484341038336/4794254402739931640625:ℝ),(28939147719596367675001046656/4794254402739931640625:ℝ),(24218537914563043165648978304/4794254402739931640625:ℝ),(2167860620484449324996323328/1598084800913310546875:ℝ)]]
theorem admission30_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (9526731242363302697737749/13405706945619804160000000000:ℝ) admission30_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission30_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_10_coefficients]
def admission30_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5937454812570340590042463867941482/80337961932348784308085414587:ℝ),(34594380165038038721813712632639872/241013885797046352924256243761:ℝ),(1865683921300329720125544777441280/26779320644116261436028471529:ℝ)],
![(5558353844020053100064078437494212/80337961932348784308085414587:ℝ),(32355489755013391829897141542074112/241013885797046352924256243761:ℝ),(1743249063871046389316354677815296/26779320644116261436028471529:ℝ)]]
theorem admission30_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2553587495904853109350128922581/13711012169787525855246577422848:ℝ) admission30_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission30_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_11_coefficients]
def admission30_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission30_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission30_12_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission30_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_12_coefficients]
def admission30_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4510254983728566477/1000000000000000000000:ℝ)]]
theorem admission30_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4510254983728566477/1000000000000000000000:ℝ) admission30_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission30_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_13_coefficients]
def admission30_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission30_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission30_14_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission30_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_14_coefficients]
theorem admission30_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission30_00_pos hδ hp
 · exact admission30_01_pos hδ hp
 · exact admission30_02_pos hδ hp
 · exact admission30_03_pos hδ hp
 · exact admission30_04_pos hδ hp
 · exact admission30_05_pos hδ hp
 · exact admission30_06_pos hδ hp
 · exact admission30_07_pos hδ hp
 · exact admission30_08_pos hδ hp
 · exact admission30_09_pos hδ hp
 · exact admission30_10_pos hδ hp
 · exact admission30_11_pos hδ hp
 · exact admission30_12_pos hδ hp
 · exact admission30_13_pos hδ hp
 · exact admission30_14_pos hδ hp
#print axioms admission30_all
end
end LewkoStage1Finite
