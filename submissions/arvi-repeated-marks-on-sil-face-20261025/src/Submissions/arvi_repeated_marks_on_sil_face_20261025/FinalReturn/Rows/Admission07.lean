/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission07_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission07_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission07_00_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission07_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_00_coefficients]
def admission07_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission07_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission07_01_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission07_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_01_coefficients]
def admission07_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission07_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission07_02_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission07_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_02_coefficients]
def admission07_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(33856801409587667954223776/9190091093611410197319:ℝ), (44500300270558794017305760/9190091093611410197319:ℝ), (3627805244708562021027328/3063363697870470065773:ℝ)],
![(22876025271100107017456000/9190091093611410197319:ℝ), (22623481194095307017456000/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission07_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (189923324268691522476615/196055276663710084209472:ℝ) admission07_03_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission07_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_03_coefficients]
def admission07_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1188263597410587234875707437/1914602311169043791108125:ℝ), (608:ℝ), (0:ℝ)],
![(1905213832789115714085806572/1914602311169043791108125:ℝ), (2534165571230446328426692224/1914602311169043791108125:ℝ), (654410046041129151058746112/1914602311169043791108125:ℝ)]]
theorem admission07_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (145708486813845162540423939/980276383318550421047360000:ℝ) admission07_04_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission07_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_04_coefficients]
def admission07_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1288636893088537120480571473/1914602311169043791108125:ℝ), (2581180211870121373511248274/1914602311169043791108125:ℝ), (1280848598770384923148709364/1914602311169043791108125:ℝ)],
![(0:ℝ), (14426190532414675629723584/382920462233808758221625:ℝ), (11964144214267448286151492/382920462233808758221625:ℝ)]]
theorem admission07_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1065354432739656694491137709/12547537706477445389406208000:ℝ) admission07_05_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission07_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_05_coefficients]
def admission07_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6258390781243872293147234913308385451603233751361056/130205735392850138427482678915942806876964464875:ℝ), (20426012898977965973810978605668786331944664990728416/217009558988083564045804464859904678128274108125:ℝ), (30001351607500093686581727637949886893017826215379968/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(634303231599308715245064360329330615028788745994624/10015825799450010648267898378149446682843420375:ℝ), (6000090614164988345080269644800511065515433192511104/43401911797616712809160892971980935625654821625:ℝ), (11536530746787504934850296330746105895367669754417152/130205735392850138427482678915942806876964464875:ℝ), (592995616130618979553882315472802150331874624937984/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission07_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (4744574990512729128831874112474478493526419729209/22221778840379756958290377201654239040335268672000:ℝ) admission07_06_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission07_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_06_coefficients]
def admission07_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9655203682803124800324850843802909561414529850369/3519073929536490227769802132863319104782823375:ℝ), (69623315264772863566337931048563491053401780132128/17595369647682451138849010664316595523914116875:ℝ), (1453804708363719187018652172367788426907548024576/1173024643178830075923267377621106368260941125:ℝ)],
![(994806091382114648990127792936827113150153031852/703814785907298045553960426572663820956564675:ℝ), (4887630016027624582293921104502251482502748342656/3519073929536490227769802132863319104782823375:ℝ), (0:ℝ)]]
theorem admission07_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (13250824164773482173347090112727238266084422099/30029430865378049943635644867100323027480092800:ℝ) admission07_07_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission07_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_07_coefficients]
def admission07_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (1207867729658799521190199123846331874100122214868206291896633230177079593/440833966987325157367767659330304236464081521029939200000000000000000:ℝ), (14524018639193625442483050305659081225706079696189542006799877530760927009/2645003801923950944206605955981825418784489126179635200000000000000000:ℝ), (7264404514551762420740401065680339608127287163609286375747491909698449451/2645003801923950944206605955981825418784489126179635200000000000000000:ℝ)],
![(8375757423374601486045758374421218362519326620946839342907518741606038717/881667933974650314735535318660608472928163042059878400000000000000000:ℝ), (2028579140305999224584110942422388939879923535502357731446136140676596907/67820610305742331902733486050816036379089464773836800000000000000000:ℝ), (82992899836830946397482375653346288610786813391567573581627624394283521793/2645003801923950944206605955981825418784489126179635200000000000000000:ℝ), (28992524849032290681469371920135985176735081429425594947453411932714358571/2645003801923950944206605955981825418784489126179635200000000000000000:ℝ)]]
theorem admission07_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (728994674975650096801952261968881907794566361764182531964888793327727829/3697983342141611713696514729199464760436485959963916212633600000000000000000:ℝ) admission07_08_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission07_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_08_coefficients]
def admission07_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(139949201592618045177533679943585107348186073269470011/8797684823841225569424505332158297761957058437500:ℝ), (24031471456683618609120754315378317050816707973641657/586512321589415037961633688810553184130470562500:ℝ), (75504616447886391065765881734438125431977911983949816/2199421205960306392356126333039574440489264609375:ℝ), (1358808581704137827642317964678963971561749882522432/146628080397353759490408422202638296032617640625:ℝ)],
![(2332478606653136742130944531047364829429809873455561/439884241192061278471225266607914888097852921875:ℝ), (1545332687570052243560920579474259506925477780638399/146628080397353759490408422202638296032617640625:ℝ), (2301786857723391601459544274213572376617260765791136/439884241192061278471225266607914888097852921875:ℝ), (0:ℝ)]]
theorem admission07_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (9062319311362207678027020678201636798946678797321/480470893846048799098170317873605168439681484800000:ℝ) admission07_09_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission07_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_09_coefficients]
def admission07_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(138988664780383916654600475152/689256832020855764798925:ℝ), (8872824816782910009225915895568/17231420800521394119973125:ℝ), (7347453178079685617342725903232/17231420800521394119973125:ℝ), (1949926179431590446081821886464/17231420800521394119973125:ℝ)],
![(195524424781116816386467508096/689256832020855764798925:ℝ), (786061153022849048143329116288/1148761386701426274664875:ℝ), (597484785607433686638972296192/1148761386701426274664875:ℝ), (31702902836150434509174390784/265098781546482986461125:ℝ)],
![(17156201637543528538561694464/229752277340285254932975:ℝ), (102176726944735391567310084352/689256832020855764798925:ℝ), (779728654403851020794230784/10603951261859319458445:ℝ), (0:ℝ)]]
theorem admission07_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3773472021825627372898801/1254753770647744538940620800:ℝ) admission07_10_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission07_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_10_coefficients]
def admission07_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(41031004566519446766573382905637206895551913511803/17595369647682451138849010664316595523914116875:ℝ), (19724725359012750663574128512687164746768782071456/5865123215894150379616336888105531841304705625:ℝ), (6196043933552235389759585684167182863983575864576/5865123215894150379616336888105531841304705625:ℝ)],
![(4206401353601868919038914493983460523988134482212/3519073929536490227769802132863319104782823375:ℝ), (1374373180349159193912405989224428772182691474304/1173024643178830075923267377621106368260941125:ℝ), (0:ℝ)]]
theorem admission07_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2203532069377677812871691900744443182574780793/6005886173075609988727128973420064605496018560:ℝ) admission07_11_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission07_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_11_coefficients]
def admission07_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission07_12_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission07_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_12_coefficients]
def admission07_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission07_13_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission07_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_13_coefficients]
def admission07_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission07_14_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission07_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_14_coefficients]
theorem admission07_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission07_00_pos hδ hp
 · exact admission07_01_pos hδ hp
 · exact admission07_02_pos hδ hp
 · exact admission07_03_pos hδ hp
 · exact admission07_04_pos hδ hp
 · exact admission07_05_pos hδ hp
 · exact admission07_06_pos hδ hp
 · exact admission07_07_pos hδ hp
 · exact admission07_08_pos hδ hp
 · exact admission07_09_pos hδ hp
 · exact admission07_10_pos hδ hp
 · exact admission07_11_pos hδ hp
 · exact admission07_12_pos hδ hp
 · exact admission07_13_pos hδ hp
 · exact admission07_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
