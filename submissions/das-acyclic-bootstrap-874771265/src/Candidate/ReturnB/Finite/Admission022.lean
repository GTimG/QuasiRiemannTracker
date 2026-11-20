/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission022_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(918998232275615744/491503911:ℝ),(8173317973788852224/1474511733:ℝ),(8075651857097162752/1474511733:ℝ),(2659328580135157760/1474511733:ℝ)],
![(1837996464551231488/491503911:ℝ),(16346635947577704448/1474511733:ℝ),(16151303714194325504/1474511733:ℝ),(5318657160270315520/1474511733:ℝ)],
![(918998232275615744/491503911:ℝ),(8173317973788852224/1474511733:ℝ),(8075651857097162752/1474511733:ℝ),(2659328580135157760/1474511733:ℝ)]]
theorem admission022_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (619173185/655338548:ℝ) admission022_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission022_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_00_coefficients]
def admission022_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2009351263468126208/1474511733:ℝ),(5974366699204378624/1474511733:ℝ),(5920679608004378624/1474511733:ℝ),(217296019140902912/163834637:ℝ)],
![(4018702526936252416/1474511733:ℝ),(11948733398408757248/1474511733:ℝ),(11841359216008757248/1474511733:ℝ),(434592038281805824/163834637:ℝ)],
![(2009351263468126208/1474511733:ℝ),(5974366699204378624/1474511733:ℝ),(5920679608004378624/1474511733:ℝ),(217296019140902912/163834637:ℝ)]]
theorem admission022_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (113834637/163834637:ℝ) admission022_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission022_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_01_coefficients]
def admission022_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3180243941907431948288/4607849165625:ℝ),(5255308102910108237824/2559916203125:ℝ),(15630628907923489685504/7679748609375:ℝ),(15495333507116654657536/23039245828125:ℝ)],
![(6360487883814863896576/4607849165625:ℝ),(10510616205820216475648/2559916203125:ℝ),(31261257815846979371008/7679748609375:ℝ),(30990667014233309315072/23039245828125:ℝ)],
![(3180243941907431948288/4607849165625:ℝ),(5255308102910108237824/2559916203125:ℝ),(15630628907923489685504/7679748609375:ℝ),(15495333507116654657536/23039245828125:ℝ)]]
theorem admission022_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (115449231170987/327669274000000:ℝ) admission022_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission022_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_02_coefficients]
def admission022_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1505032723330236416/1474511733:ℝ),(13312704206430273536/4423535199:ℝ),(13081323042088419328/4423535199:ℝ),(4283717005648855040/4423535199:ℝ)],
![(2970551436587302912/1474511733:ℝ),(26270064638987075584/4423535199:ℝ),(25807614118288424960/4423535199:ℝ),(8449203789063258112/4423535199:ℝ)],
![(1465518713257066496/1474511733:ℝ),(12957360432556802048/4423535199:ℝ),(12726291076200005632/4423535199:ℝ),(4165486783414403072/4423535199:ℝ)]]
theorem admission022_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (124141180021/251650002432:ℝ) admission022_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission022_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_03_coefficients]
def admission022_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1351907894335666502144/7679748609375:ℝ),(788727467146349244928/1535949721875:ℝ),(3832566694895655583744/7679748609375:ℝ),(1240837253499575861248/7679748609375:ℝ)],
![(110682139008155995648/307189944375:ℝ),(8074253917713016200704/7679748609375:ℝ),(7849403596020442464256/7679748609375:ℝ),(847401051170442051584/2559916203125:ℝ)],
![(1415145580868233389056/7679748609375:ℝ),(1376872193993756658688/2559916203125:ℝ),(1338945633708262293504/2559916203125:ℝ),(1301365900011750293504/7679748609375:ℝ)]]
theorem admission022_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (14200255434031401/167766668288000000:ℝ) admission022_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission022_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_04_coefficients]
def admission022_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(386409133071589574656/4607849165625:ℝ),(5829665220945908847616/23039245828125:ℝ),(5861720096740486152704/23039245828125:ℝ),(654700180384175059456/7679748609375:ℝ)],
![(3520088409910614413824/23039245828125:ℝ),(2127178114492211241472/4607849165625:ℝ),(10708533281691939963904/23039245828125:ℝ),(1197577039713832723456/7679748609375:ℝ)],
![(1588042744552666540544/23039245828125:ℝ),(4806225351515147359744/23039245828125:ℝ),(193872527398058152448/921569833125:ℝ),(1447671624879087104/20479329625:ℝ)]]
theorem admission022_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (3101645985454426837/85896534163456000000:ℝ) admission022_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission022_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_05_coefficients]
def admission022_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(112756131496931425827490562558464/418983538947513237984375:ℝ),(107811920316819040637701552008704/139661179649171079328125:ℝ),(308885382747363106481329054220288/418983538947513237984375:ℝ),(2182316658623324817682554683392/9310745309944738621875:ℝ)],
![(230212639179239952106339439693312/418983538947513237984375:ℝ),(220246970229058750666545126840832/139661179649171079328125:ℝ),(631413098768903821279661069369344/418983538947513237984375:ℝ),(4464039628330233879697002856448/9310745309944738621875:ℝ)],
![(117456507682308526278848877134848/418983538947513237984375:ℝ),(112435049912239710028843574832128/139661179649171079328125:ℝ),(322527716021540714798332015149056/418983538947513237984375:ℝ),(2281722969706909062014448173056/9310745309944738621875:ℝ)]]
theorem admission022_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (24974632171134851276579529/203396334877512796774400000:ℝ) admission022_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission022_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_06_coefficients]
def admission022_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(618760522073081046533072195072/1258208825668207921875:ℝ),(16382126845601373377910932176384/11323879431013871296875:ℝ),(16060162225199149788485278171136/11323879431013871296875:ℝ),(209875203130220233174879830016/452955177240554851875:ℝ)],
![(399618422657194134850203090432/419402941889402640625:ℝ),(31731051407010668353748682394112/11323879431013871296875:ℝ),(31097814718175298711077562155008/11323879431013871296875:ℝ),(2031292144581774399656872640512/2264775886202774259375:ℝ)],
![(580094745898501358017537076224/1258208825668207921875:ℝ),(15348924561409294975837750217728/11323879431013871296875:ℝ),(15037652492976148922592283983872/11323879431013871296875:ℝ),(981916128930673233782473490432/2264775886202774259375:ℝ)]]
theorem admission022_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1872856386052462070050189/8245797359899167436800000:ℝ) admission022_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission022_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_07_coefficients]
def admission022_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13656610812956298389994993857775301/1965951290106574877929687500:ℝ),(1979021801740604162352812550031525999/88467808054795869506835937500:ℝ),(704946211766425166398177082310953183/29489269351598623168945312500:ℝ),(150061041428970980796389812551494419/17693561610959173901367187500:ℝ)],
![(9990210240130134944130100643412929/491487822526643719482421875:ℝ),(1406315611275769338457006087977521528/22116952013698967376708984375:ℝ),(976217716928805256747205505543542687/14744634675799311584472656250:ℝ),(203016203191906778357442724368424723/8846780805479586950683593750:ℝ)],
![(5260846029512848277305081743175283/393190258021314975585937500:ℝ),(3646240643362473191475211801878560113/88467808054795869506835937500:ℝ),(1247489222091185347096233928776132191/29489269351598623168945312500:ℝ),(255971364954842575918495636185355027/17693561610959173901367187500:ℝ)]]
theorem admission022_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (40969832438868895169984981573325903/11258261995382329940377600000000000000:ℝ) admission022_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission022_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_08_coefficients]
def admission022_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4830702545387244003633109248152/283096985775346782421875:ℝ),(1696615196912592407350757336862944/35387123221918347802734375:ℝ),(527461816987535632879965143861248/11795707740639449267578125:ℝ),(19585132547128477734778884718592/1415484928876733912109375:ℝ)],
![(192302488786966557562330461649096/7077424644383669560546875:ℝ),(2671202495041238448014544615036832/35387123221918347802734375:ℝ),(819653502563055558425845154699264/11795707740639449267578125:ℝ),(149862286637272846844071145996288/7077424644383669560546875:ℝ)],
![(71534925152285457471502730445296/7077424644383669560546875:ℝ),(974587298128646040663787278173888/35387123221918347802734375:ℝ),(292191685575519925545880010838016/11795707740639449267578125:ℝ),(51936623901630458170176722403328/7077424644383669560546875:ℝ)]]
theorem admission022_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1584979977466749822087912671/412289867994958371840000000000:ℝ) admission022_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission022_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_09_coefficients]
def admission022_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(335694979851239259978478/71997643212890625:ℝ),(20591728349889381436054/1599947626953125:ℝ),(846463725740664658328176/71997643212890625:ℝ),(255540976448444253684224/71997643212890625:ℝ)],
![(508320725792226625813336/71997643212890625:ℝ),(152572204334071501341528/7999738134765625:ℝ),(1221793966366957269282496/71997643212890625:ℝ),(71397087286758076604416/14399528642578125:ℝ)],
![(18710084562919993591992/7999738134765625:ℝ),(48231885672720351207032/7999738134765625:ℝ),(121053890514521737939264/23999214404296875:ℝ),(32492001403870665094144/23999214404296875:ℝ)]]
theorem admission022_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (95191410362902339143/134213334630400000000000:ℝ) admission022_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission022_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_10_coefficients]
def admission022_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4574795020129907306390937108992/11323879431013871296875:ℝ),(4486685806168832989164523443712/3774626477004623765625:ℝ),(4399357484562203878087842562048/3774626477004623765625:ℝ),(34502480442480159785287155712/90591035448110970375:ℝ)],
![(8857557107808833828153055098368/11323879431013871296875:ℝ),(8684391477733118121897998094848/3774626477004623765625:ℝ),(8512759779556873499577232818176/3774626477004623765625:ℝ),(8342662013280099961190759268352/11323879431013871296875:ℝ)],
![(4282762087678926521762117989376/11323879431013871296875:ℝ),(4197705671564285132733474651136/3774626477004623765625:ℝ),(4113402294994669621489390256128/3774626477004623765625:ℝ),(4029851957970079988029864804352/11323879431013871296875:ℝ)]]
theorem admission022_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (7686332622471008277950029/41228986799495837184000000:ℝ) admission022_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission022_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_11_coefficients]
def admission022_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)],
![(13801977297240064/439453125:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/439453125:ℝ)],
![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)]]
theorem admission022_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission022_12_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission022_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_12_coefficients]
def admission022_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2413484811481513984/274658203125:ℝ),(2413484811481513984/91552734375:ℝ),(2413484811481513984/91552734375:ℝ),(2413484811481513984/274658203125:ℝ)],
![(4826969622963027968/274658203125:ℝ),(4826969622963027968/91552734375:ℝ),(4826969622963027968/91552734375:ℝ),(4826969622963027968/274658203125:ℝ)],
![(2413484811481513984/274658203125:ℝ),(2413484811481513984/91552734375:ℝ),(2413484811481513984/91552734375:ℝ),(2413484811481513984/274658203125:ℝ)]]
theorem admission022_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (4603356955493/1000000000000000:ℝ) admission022_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission022_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_13_coefficients]
def admission022_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission022_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission022_14_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission022_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_14_coefficients]
theorem admission022_all {δ p : ℝ}
 (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .P δ p j := by
 intro j
 fin_cases j
 · exact admission022_00_pos hd hp
 · exact admission022_01_pos hd hp
 · exact admission022_02_pos hd hp
 · exact admission022_03_pos hd hp
 · exact admission022_04_pos hd hp
 · exact admission022_05_pos hd hp
 · exact admission022_06_pos hd hp
 · exact admission022_07_pos hd hp
 · exact admission022_08_pos hd hp
 · exact admission022_09_pos hd hp
 · exact admission022_10_pos hd hp
 · exact admission022_11_pos hd hp
 · exact admission022_12_pos hd hp
 · exact admission022_13_pos hd hp
 · exact admission022_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission022_all
