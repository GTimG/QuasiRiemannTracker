/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission31_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20148293628876163/163653997694883:ℝ), (19784639631181280/163653997694883:ℝ)]]
theorem admission31_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618269988474415/654615990779532:ℝ) admission31_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission31_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_00_coefficients]
def admission31_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(14747711704945024/163653997694883:ℝ), (14547711704945024/163653997694883:ℝ)]]
theorem admission31_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113653997694883/163653997694883:ℝ) admission31_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission31_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_01_coefficients]
def admission31_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7474945888644010/163653997694883:ℝ), (7378206857552768/163653997694883:ℝ)]]
theorem admission31_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57642241074631/163653997694883:ℝ) admission31_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission31_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_02_coefficients]
def admission31_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1072408403173759957376/1472885979253947:ℝ), (235177262804136709504/163653997694883:ℝ), (1044260762063470428160/1472885979253947:ℝ)],
![(1043543486752959461120/1472885979253947:ℝ), (228767089221142765312/163653997694883:ℝ), (1015435916237325426688/1472885979253947:ℝ)]]
theorem admission31_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123954579618814139/251372540459340288:ℝ) admission31_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission31_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_03_coefficients]
def admission31_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20223237274395950138/163653997694883:ℝ), (39579685768339672448/163653997694883:ℝ), (19360414794218463232/163653997694883:ℝ)],
![(21188692202898740708/163653997694883:ℝ), (41489454435578126080/163653997694883:ℝ), (20304825271985217536/163653997694883:ℝ)]]
theorem admission31_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2363331884059871/27930282273260032:ℝ) admission31_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission31_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_04_coefficients]
def admission31_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(419911721697647398824/6818916570620125:ℝ), (37948005138331744456852/306851245677905625:ℝ), (19048383061422472281022/306851245677905625:ℝ)],
![(1731446641588163865778/34094582853100625:ℝ), (31363621927778043921388/306851245677905625:ℝ), (15776919879786133821886/306851245677905625:ℝ)]]
theorem admission31_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2597169962382245798667/71501522619545681920000:ℝ) admission31_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission31_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_05_coefficients]
def admission31_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(210176675852595055745474534278312385024/8918616110185084502428939768437:ℝ), (68445948011853742021028434776310204928/990957345576120500269882196493:ℝ), (601636823734780211127999593506676523008/8918616110185084502428939768437:ℝ), (195799591753381170331102614798197063680/8918616110185084502428939768437:ℝ)],
![(219320996219357563201473861319953425408/8918616110185084502428939768437:ℝ), (71468883925798361804884852705391707136/990957345576120500269882196493:ℝ), (628619020046364069813220162638114553856/8918616110185084502428939768437:ℝ), (204719676042145216506563149609542615040/8918616110185084502428939768437:ℝ)]]
theorem admission31_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (373458083636057224905209760280985/3044220965609842176829078107626496:ℝ) admission31_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission31_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_06_coefficients]
def admission31_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(84247232600730527164298627209242274/241043678653650932498079453201:ℝ), (165983790675195496176602791109264768/241043678653650932498079453201:ℝ), (81746091728555512599984033318502400/241043678653650932498079453201:ℝ)],
![(78909062984892693385110502655574388/241043678653650932498079453201:ℝ), (155390831778340456010728203145039616/241043678653650932498079453201:ℝ), (76490985831719801075699345462312960/241043678653650932498079453201:ℝ)]]
theorem admission31_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4668639271955554264874227628315/20569060578444879573169446673152:ℝ) admission31_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission31_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_07_coefficients]
def admission31_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(98474056724032269208896123255494960739463428512785439/139492869591233178528981165046875000000000000000:ℝ), (2748276621827672460258920895300235272762477846426290153/1255435826321098606760830485421875000000000000000:ℝ), (8513616061993157216787356071408706953435926340959385393/3766307478963295820282491456265625000000000000000:ℝ), (2927556218807016651796292760880306712461633496525721787/3766307478963295820282491456265625000000000000000:ℝ)],
![(179560809902703326285122005472936935200728347509925677/139492869591233178528981165046875000000000000000:ℝ), (4911288368626573684424892312182371146046388962440718439/1255435826321098606760830485421875000000000000000:ℝ), (2984855270908412829990221269006876178643173713064326973/753261495792659164056498291253125000000000000000:ℝ), (5038522887045484930279874043912797602291498310767472827/3766307478963295820282491456265625000000000000000:ℝ)]]
theorem admission31_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (98474056724032269208896123255494960739463428512785439/24963221371647474587170978836512768000000000000000000000:ℝ) admission31_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission31_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_08_coefficients]
def admission31_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2262295360927859025979783876165440517287703/1569294782901373258451038106777343750:ℝ), (6549520071802474666472674910155862670066059/1569294782901373258451038106777343750:ℝ), (1052147539374589277908593250865211964749376/261549130483562209741839684462890625:ℝ), (40513420699278829235873157085261671620608/31385895658027465169020762135546875:ℝ)],
![(636682396654385421804038088623488337742443/784647391450686629225519053388671875:ℝ), (1808220911814232418584408773895344761233999/784647391450686629225519053388671875:ℝ), (568877881977915687080599743853202991225472/261549130483562209741839684462890625:ℝ), (107020102747030989143674865571242767849472/156929478290137325845103810677734375:ℝ)]]
theorem admission31_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52255909544448725167809992954708382739/13712707052296586382112964448768000000000:ℝ) admission31_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission31_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_09_coefficients]
def admission31_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(157512924609562427036296759616/4794550713717275390625:ℝ), (1353588089036429799436172176448/14383652141151826171875:ℝ), (1289683316726032175612878516352/14383652141151826171875:ℝ), (136212003612867385761865539584/4794550713717275390625:ℝ)],
![(230595060521937081482479747328/4794550713717275390625:ℝ), (1954468631488653806987325463808/14383652141151826171875:ℝ), (1833777052556760641975953201664/14383652141151826171875:ℝ), (38073181286011205295737798656/958910142743455078125:ℝ)],
![(4726545893721326252536808192/319636714247818359375:ℝ), (193812657126171141256986620672/4794550713717275390625:ℝ), (174954263200892810555956872704/4794550713717275390625:ℝ), (17346832441430521029007458304/1598183571239091796875:ℝ)]]
theorem admission31_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3176299885515842473573143/4468845163721605120000000000:ℝ) admission31_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission31_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_10_coefficients]
def admission31_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(69209125445540625986576050680645598/241043678653650932498079453201:ℝ), (136375665534742563878803344258216704/241043678653650932498079453201:ℝ), (67175679894390953078361567537889280/241043678653650932498079453201:ℝ)],
![(64730296215559858568086349790417292/241043678653650932498079453201:ℝ), (127488791182880762541545680709250560/241043678653650932498079453201:ℝ), (62767308550620645036591829324783616/241043678653650932498079453201:ℝ)]]
theorem admission31_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (7662024969558184208568338540623/41138121156889759146338893346304:ℝ) admission31_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission31_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_11_coefficients]
def admission31_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission31_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission31_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission31_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_12_coefficients]
def admission31_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4506816185952085117/1000000000000000000000:ℝ)]]
theorem admission31_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4506816185952085117/1000000000000000000000:ℝ) admission31_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
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
end Record1252270103Finite
