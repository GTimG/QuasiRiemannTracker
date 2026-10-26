/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission27_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(5309813905490203/163653997694883:ℝ), (4946159907795320/163653997694883:ℝ)]]
theorem admission27_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618269988474415/654615990779532:ℝ) admission27_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission27_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_00_coefficients]
def admission27_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3836927926236256/163653997694883:ℝ), (3636927926236256/163653997694883:ℝ)]]
theorem admission27_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113653997694883/163653997694883:ℝ) admission27_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission27_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_01_coefficients]
def admission27_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1941290745479434/163653997694883:ℝ), (1844551714388192/163653997694883:ℝ)]]
theorem admission27_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57642241074631/163653997694883:ℝ) admission27_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission27_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_02_coefficients]
def admission27_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37084389209668610176/1472885979253947:ℝ), (23527438152073030784/490961993084649:ℝ), (33533925246550482176/1472885979253947:ℝ)],
![(35274168696870673888/1472885979253947:ℝ), (22322913693095697824/490961993084649:ℝ), (31732372382416419584/1472885979253947:ℝ)]]
theorem admission27_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123954579618814139/251372540459340288:ℝ) admission27_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission27_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_03_coefficients]
def admission27_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(696929887750771400/163653997694883:ℝ), (1285251655733168000/163653997694883:ℝ), (590256548604221440/163653997694883:ℝ)],
![(761289209568521042/163653997694883:ℝ), (1408539893380248544/163653997694883:ℝ), (649282203464643584/163653997694883:ℝ)]]
theorem admission27_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (288211205373155/3491285284157504:ℝ) admission27_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission27_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_04_coefficients]
def admission27_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(230702736013023070604/102283748559301875:ℝ), (1401136360564003634624/306851245677905625:ℝ), (707274688859012847812/306851245677905625:ℝ)],
![(159063291394415358356/102283748559301875:ℝ), (981839251039205422934/306851245677905625:ℝ), (502808240006741694116/306851245677905625:ℝ)]]
theorem admission27_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (39765822848603839589/1117211290930401280000:ℝ) admission27_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission27_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_05_coefficients]
def admission27_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1950073848682270647605788831354954240/8918616110185084502428939768437:ℝ), (48446615422297970508980912363261440/80347892884550310832693151067:ℝ), (4922523976127948137761938904971161600/8918616110185084502428939768437:ℝ), (1494840231320305837838846464004096000/8918616110185084502428939768437:ℝ)],
![(2103901662262183092738451864593342592/8918616110185084502428939768437:ℝ), (1941339020242951404496173770667514240/2972872036728361500809646589479:ℝ), (5354524392494495312164086767840570368/8918616110185084502428939768437:ℝ), (1634216548332244059330417320431370240/8918616110185084502428939768437:ℝ)]]
theorem admission27_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (45618903543710505305140578125125/380527620701230272103634763453312:ℝ) admission27_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission27_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_06_coefficients]
def admission27_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3045506850906511128264936559278440/241043678653650932498079453201:ℝ), (5759369141745462519509287163931520/241043678653650932498079453201:ℝ), (2718787425793475753883397536709120/241043678653650932498079453201:ℝ)],
![(2696059340739869741072616059672858/241043678653650932498079453201:ℝ), (5081794128845094299647398118946272/241043678653650932498079453201:ℝ), (2390343307241243783615604545697280/241043678653650932498079453201:ℝ)]]
theorem admission27_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4668639271955554264874227628315/20569060578444879573169446673152:ℝ) admission27_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission27_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_07_coefficients]
def admission27_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(180938184759738886069118556227931595862552223038341/83695721754739907117388699028125000000000000000:ℝ), (784631972581275079788969279729763871818919093496251/83695721754739907117388699028125000000000000000:ℝ), (9237974819778736920822245660278474209890083783227961/753261495792659164056498291253125000000000000000:ℝ), (3801851777970818215929349877927021516295281949106771/753261495792659164056498291253125000000000000000:ℝ)],
![(10253438941430084772693809344776447635202429916127719/836957217547399071173886990281250000000000000000:ℝ), (6405942325448755633948296951962028707745803581802119/167391443509479814234777398056250000000000000000:ℝ), (150001454662165766265092002476552960903372068436034157/3766307478963295820282491456265625000000000000000:ℝ), (10398622616216031586190541387403555547013609493612243/753261495792659164056498291253125000000000000000:ℝ)]]
theorem admission27_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (180938184759738886069118556227931595862552223038341/117015100179597537127363963296153600000000000000000000:ℝ) admission27_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission27_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_08_coefficients]
def admission27_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6364135038080739556655220312295181788531/313858956580274651690207621355468750:ℝ), (17362976454556829222533333831230818793059/313858956580274651690207621355468750:ℝ), (104372326462418245420031028268017157984/2092393043868497677934717475703125:ℝ), (2329016439419978931367630510010733971536/156929478290137325845103810677734375:ℝ)],
![(59010437597701348357217625559678404309791/6277179131605493033804152427109375000:ℝ), (30250511968337159524293320962658430889859/1255435826321098606760830485421875000:ℝ), (5236015521142171180994343686282581618436/261549130483562209741839684462890625:ℝ), (836094552711179602684959887275334123824/156929478290137325845103810677734375:ℝ)]]
theorem admission27_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52255909544448725167809992954708382739/13712707052296586382112964448768000000000:ℝ) admission27_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission27_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_09_coefficients]
def admission27_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(405271516222153306695050816/1598183571239091796875:ℝ), (9817714107341847749930132032/14383652141151826171875:ℝ), (8702878651760230331593892032/14383652141151826171875:ℝ), (844362105139254113973072448/4794550713717275390625:ℝ)],
![(584099904329687221623725632/1598183571239091796875:ℝ), (13741456159618707959319247744/14383652141151826171875:ℝ), (11725554734067877575447903424/14383652141151826171875:ℝ), (1080667258638784870247395456/4794550713717275390625:ℝ)],
![(166323650250686717141694488/1598183571239091796875:ℝ), (239995019494674226655019616/958910142743455078125:ℝ), (904111628456824900158695768/4794550713717275390625:ℝ), (67761064224337972769560384/1598183571239091796875:ℝ)]]
theorem admission27_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3176299885515842473573143/4468845163721605120000000000:ℝ) admission27_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission27_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_10_coefficients]
def admission27_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2503539291016914436546927600210712/241043678653650932498079453201:ℝ), (4735807878670309191983006147586304/241043678653650932498079453201:ℝ), (2237001601192539410004103304718592/241043678653650932498079453201:ℝ)],
![(2210156944061699747504996626835078/241043678653650932498079453201:ℝ), (4167228544618724373332242090259392/241043678653650932498079453201:ℝ), (1961478392206895157393494666399488/241043678653650932498079453201:ℝ)]]
theorem admission27_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (7662024969558184208568338540623/41138121156889759146338893346304:ℝ) admission27_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission27_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_11_coefficients]
def admission27_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission27_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission27_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission27_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_12_coefficients]
def admission27_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4506816185952085117/1000000000000000000000:ℝ)]]
theorem admission27_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4506816185952085117/1000000000000000000000:ℝ) admission27_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission27_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_13_coefficients]
def admission27_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission27_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission27_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission27_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_14_coefficients]
theorem admission27_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission27_00_pos hδ hp
 · exact admission27_01_pos hδ hp
 · exact admission27_02_pos hδ hp
 · exact admission27_03_pos hδ hp
 · exact admission27_04_pos hδ hp
 · exact admission27_05_pos hδ hp
 · exact admission27_06_pos hδ hp
 · exact admission27_07_pos hδ hp
 · exact admission27_08_pos hδ hp
 · exact admission27_09_pos hδ hp
 · exact admission27_10_pos hδ hp
 · exact admission27_11_pos hδ hp
 · exact admission27_12_pos hδ hp
 · exact admission27_13_pos hδ hp
 · exact admission27_14_pos hδ hp
#print axioms admission27_all
end
end Record1252270103Finite
