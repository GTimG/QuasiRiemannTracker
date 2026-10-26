/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission30_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3418657937761841/54551332564961:ℝ), (9892319815590640/163653997694883:ℝ)]]
theorem admission30_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618269988474415/654615990779532:ℝ) admission30_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission30_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_00_coefficients]
def admission30_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2491285284157504/54551332564961:ℝ), (7273855852472512/163653997694883:ℝ)]]
theorem admission30_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113653997694883/163653997694883:ℝ) admission30_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission30_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_01_coefficients]
def admission30_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1261947486622542/54551332564961:ℝ), (3689103428776384/163653997694883:ℝ)]]
theorem admission30_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57642241074631/163653997694883:ℝ) admission30_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission30_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_02_coefficients]
def admission30_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(91725303690337457216/490961993084649:ℝ), (536167301586879978688/1472885979253947:ℝ), (261065190515867607040/1472885979253947:ℝ)],
![(89316854772382791296/490961993084649:ℝ), (521733943376479730560/1472885979253947:ℝ), (253858979059331356672/1472885979253947:ℝ)]]
theorem admission30_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123954579618814139/251372540459340288:ℝ) admission30_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission30_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_03_coefficients]
def admission30_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5273498088780729722/163653997694883:ℝ), (10109635487060604608/163653997694883:ℝ), (4840103698554615808/163653997694883:ℝ)],
![(5520171303105982052/163653997694883:ℝ), (10592314581796454272/163653997694883:ℝ), (5076206317996304384/163653997694883:ℝ)]]
theorem admission30_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2363331884059871/27930282273260032:ℝ) admission30_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission30_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_04_coefficients]
def admission30_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(941855750839013998904/61370249135581125:ℝ), (9500127201677018499136/306851245677905625:ℝ), (531917094107423252874/34094582853100625:ℝ)],
![(774119372392435498478/61370249135581125:ℝ), (7843667187218337460972/306851245677905625:ℝ), (1323129350519241553694/102283748559301875:ℝ)]]
theorem admission30_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (387059686196217749239/10725228392931852288000:ℝ) admission30_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission30_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_05_coefficients]
def admission30_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(28104166763775623141458649311810960640/8918616110185084502428939768437:ℝ), (80613201093469672404791640289381559552/8918616110185084502428939768437:ℝ), (76984359026177113907836417827345231872/8918616110185084502428939768437:ℝ), (24474948969172646291387826849774632960/8918616110185084502428939768437:ℝ)],
![(29275814059587800469476671104026554880/8918616110185084502428939768437:ℝ), (84070346158715049405332936958783885824/8918616110185084502428939768437:ℝ), (80384876495786561263343859555950157824/8918616110185084502428939768437:ℝ), (25589959505268152063320393701192826880/8918616110185084502428939768437:ℝ)]]
theorem admission30_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (373458083636057224905209760280985/3044220965609842176829078107626496:ℝ) admission30_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission30_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_06_coefficients]
def admission30_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21691860195271657225993239984235490/241043678653650932498079453201:ℝ), (14039616491106663929436459631793728/80347892884550310832693151067:ℝ), (20436522932138878149996008329625600/241043678653650932498079453201:ℝ)],
![(20336393553652415648671237448632820/241043678653650932498079453201:ℝ), (13149974324436775822504809613787776/80347892884550310832693151067:ℝ), (19122746457929950268924836365578240/241043678653650932498079453201:ℝ)]]
theorem admission30_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4668639271955554264874227628315/20569060578444879573169446673152:ℝ) admission30_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission30_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_07_coefficients]
def admission30_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(126238805679676741910828164735488984523752453922110721/1506522991585318328112996582506250000000000000000:ℝ), (2027398531061624975654350210043667086315579939266020731/7532614957926591640564982912531250000000000000000:ℝ), (2161658430357818442364182489935561629489585666637645681/7532614957926591640564982912531250000000000000000:ℝ), (153078981838117654110996239703444548097604849396435711/1506522991585318328112996582506250000000000000000:ℝ)],
![(47937277554590140645336161153104726844313578241341143/301304598317063665622599316501250000000000000000:ℝ), (3688998480088272923851200149338768933759769673628369397/7532614957926591640564982912531250000000000000000:ℝ), (3783763575453420700083371664474030432007158168137457137/7532614957926591640564982912531250000000000000000:ℝ), (258627315250041068035175303855069092589098090108523263/1506522991585318328112996582506250000000000000000:ℝ)]]
theorem admission30_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (126238805679676741910828164735488984523752453922110721/33700348851724090692680821429292236800000000000000000000:ℝ) admission30_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission30_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_08_coefficients]
def admission30_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5000764075488206830114065049639066907999/25108716526421972135216609708437500:ℝ), (1755888111777895095366358795661903567342603/3138589565802746516902076213554687500:ℝ), (136432445158400978115044696824860267372944/261549130483562209741839684462890625:ℝ), (5064177587409853654484144635657708952576/31385895658027465169020762135546875:ℝ)],
![(36937115205524643842994687433476588255451/313858956580274651690207621355468750:ℝ), (502912651181851566631390288227896166993103/1569294782901373258451038106777343750:ℝ), (75331906277584553555353144981274017900448/261549130483562209741839684462890625:ℝ), (13377512843378873642959358196405345981184/156929478290137325845103810677734375:ℝ)]]
theorem admission30_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52255909544448725167809992954708382739/13712707052296586382112964448768000000000:ℝ) admission30_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission30_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_09_coefficients]
def admission30_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67086057137155155633324242368/14383652141151826171875:ℝ), (4115353115992769353194345824/319636714247818359375:ℝ), (169182325117032234921120897056/14383652141151826171875:ℝ), (17026500451608423220233192448/4794550713717275390625:ℝ)],
![(101607914049403491518256438016/14383652141151826171875:ℝ), (10166942007398504159044861056/532727857079697265625:ℝ), (244282618405377130705463182976/14383652141151826171875:ℝ), (4759147660751400661967224832/958910142743455078125:ℝ)],
![(11225363477421080412670233856/4794550713717275390625:ℝ), (3216042606583166834238696064/532727857079697265625:ℝ), (24223379303613866481355827584/4794550713717275390625:ℝ), (2168354055178815128625932288/1598183571239091796875:ℝ)]]
theorem admission30_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3176299885515842473573143/4468845163721605120000000000:ℝ) admission30_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission30_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_10_coefficients]
def admission30_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(17815212651767082316764770436009566/241043678653650932498079453201:ℝ), (11533330940058601800073629453387904/80347892884550310832693151067:ℝ), (16793919973597738269590391884472320/241043678653650932498079453201:ℝ)],
![(16677727761774638556461466766987916/241043678653650932498079453201:ℝ), (10786913772043352917492308564077824/80347892884550310832693151067:ℝ), (15691827137655161259147957331195904/241043678653650932498079453201:ℝ)]]
theorem admission30_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (7662024969558184208568338540623/41138121156889759146338893346304:ℝ) admission30_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
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
def admission30_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4506816185952085117/1000000000000000000000:ℝ)]]
theorem admission30_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4506816185952085117/1000000000000000000000:ℝ) admission30_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
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
end Record1252270103Finite
