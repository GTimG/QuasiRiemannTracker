/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def admission08_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(66368673311749/1066279917429:ℝ), (191907180182960/3198839752287:ℝ)]]
theorem admission08_00_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission08_00_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 0 := by
 rw [admission08_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_00_coefficients]
def admission08_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(48241914715456/1066279917429:ℝ), (140725744146368/3198839752287:ℝ)]]
theorem admission08_01_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission08_01_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 1 := by
 rw [admission08_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_01_coefficients]
def admission08_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8166685161316/355426639143:ℝ), (23858662025696/1066279917429:ℝ)]]
theorem admission08_02_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (745583188303/2132559834858:ℝ) admission08_02_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 2 := by
 rw [admission08_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_02_coefficients]
def admission08_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1873099158794714176/9596519256861:ℝ), (10958140803713868992/28789557770583:ℝ), (5340175327329726464/28789557770583:ℝ)],
![(1826284321712999296/9596519256861:ℝ), (10677641249526262400/28789557770583:ℝ), (5200156284387264512/28789557770583:ℝ)]]
theorem admission08_03_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2539138810735969/4913417859512832:ℝ) admission08_03_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 3 := by
 rw [admission08_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_03_coefficients]
def admission08_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(30797338240851260/1066279917429:ℝ), (59022262521320000/1066279917429:ℝ), (28248655838424064/1066279917429:ℝ)],
![(32393175918669512/1066279917429:ℝ), (20714804391774848/355426639143:ℝ), (9925203402689536/355426639143:ℝ)]]
theorem admission08_04_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (27586577967211/363956878482432:ℝ) admission08_04_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 4 := by
 rw [admission08_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_04_coefficients]
def admission08_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24744257402866569184/1199564907107625:ℝ), (247311258420671830508/5997824535538125:ℝ), (41175276214280095696/1999274845179375:ℝ)],
![(4297312308396193424/239912981421525:ℝ), (215145652952004002312/5997824535538125:ℝ), (35882322963465933904/1999274845179375:ℝ)]]
theorem admission08_05_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (268582019274762089/5240979050147020800:ℝ) admission08_05_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 5 := by
 rw [admission08_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_05_coefficients]
def admission08_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9641437879849293026969282966463616/3407447728350247988736212877:ℝ), (27604831930567561205139652379055232/3407447728350247988736212877:ℝ), (26310837084157221724397416713220096/3407447728350247988736212877:ℝ), (8347308789475252898251047300628480/3407447728350247988736212877:ℝ)],
![(10081577902286229388988669244477184/3407447728350247988736212877:ℝ), (28903245997783156443853078631296768/3407447728350247988736212877:ℝ), (27587698180823733603125905860665344/3407447728350247988736212877:ℝ), (8765892213147870747637496473845760/3407447728350247988736212877:ℝ)]]
theorem admission08_06_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (63684912029077552019127252965/581537745638442323410980331008:ℝ) admission08_06_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 6 := by
 rw [admission08_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_06_coefficients]
def admission08_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3076156807162294687894185175196/30697727282434666565191107:ℝ), (1989481728190336288982177767616/10232575760811555521730369:ℝ), (2893705885047019427348846981120/30697727282434666565191107:ℝ)],
![(2905976735178770255901022780424/30697727282434666565191107:ℝ), (1877825106767858789889642287744/10232575760811555521730369:ℝ), (2728874537164594270094798735360/30697727282434666565191107:ℝ)]]
theorem admission08_07_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1332458270099899545944725945/5239078789535516427125948928:ℝ) admission08_07_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 7 := by
 rw [admission08_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_07_coefficients]
def admission08_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(35765437821381173143787433020879513805371082377/11511647730912999961946665125000000000000000:ℝ), (2463671975517489341362658298316544996878488936403/57558238654564999809733325625000000000000000:ℝ), (4378168274285308529992467439885285447485904161913/57558238654564999809733325625000000000000000:ℝ), (418580346561450887853365012711385925851854127479/11511647730912999961946665125000000000000000:ℝ)],
![(876454783040075407915997674090116786901888349363/11511647730912999961946665125000000000000000:ℝ), (14769644770616387593824982176018060459142575217957/57558238654564999809733325625000000000000000:ℝ), (16384571671269028139501712047131108965851297609977/57558238654564999809733325625000000000000000:ℝ), (1199353532399987931250732798375343143193632827767/11511647730912999961946665125000000000000000:ℝ)]]
theorem admission08_08_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (35765437821381173143787433020879513805371082377/257511200663249703426094641709056000000000000000000:ℝ) admission08_08_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 8 := by
 rw [admission08_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_08_coefficients]
def admission08_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2587438488250172364485313828155451343963/7194779831820624976216665703125000:ℝ), (36664506825941326672861151591546449306727/35973899159103124881083328515625000:ℝ), (4317266807367487794711341937526630228024/4496737394887890610135416064453125:ℝ), (270275886995468567436373108574338418432/899347478977578122027083212890625:ℝ)],
![(1003404494194618460754005575670109988781/3597389915910312488108332851562500:ℝ), (14075570270842760023543977828229781746369/17986949579551562440541664257812500:ℝ), (3277237787739551218143273777803260394896/4496737394887890610135416064453125:ℝ), (202525698237963071982898683170831113856/899347478977578122027083212890625:ℝ)]]
theorem admission08_09_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1582232017484086499866395962272118077/157172363686065492813778467840000000000:ℝ) admission08_09_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 9 := by
 rw [admission08_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_09_coefficients]
def admission08_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4074169910057662214426516368/468580041838916015625:ℝ), (34483919200697456492741368384/1405740125516748046875:ℝ), (32315677624084366032156589456/1405740125516748046875:ℝ), (1117159087982349575854974464/156193347279638671875:ℝ)],
![(21947606510735144242180904768/1405740125516748046875:ℝ), (50708620005421716219631872/1156987757626953125:ℝ), (6378647257097917251723637184/156193347279638671875:ℝ), (17744794639904014300840914944/1405740125516748046875:ℝ)],
![(9643109671583684130079212224/1405740125516748046875:ℝ), (26886346569231166451950087424/1405740125516748046875:ℝ), (24856627620278999854112538176/1405740125516748046875:ℝ), (7613563325756517532241662976/1405740125516748046875:ℝ)]]
theorem admission08_10_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7435120435309099152579749/2620489525073510400000000000:ℝ) admission08_10_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 10 := by
 rw [admission08_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_10_coefficients]
def admission08_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2523835865024001621964497744548/30697727282434666565191107:ℝ), (1632412752962200370969815799552/10232575760811555521730369:ℝ), (2374766058768370788992159375360/30697727282434666565191107:ℝ)],
![(2380979075204811384142751559032/30697727282434666565191107:ℝ), (1538711667532339090496917733888/10232575760811555521730369:ℝ), (2236476581490472689364815564800/30697727282434666565191107:ℝ)]]
theorem admission08_11_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (546014790402947433926956925/2619539394767758213562974464:ℝ) admission08_11_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 11 := by
 rw [admission08_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_11_coefficients]
def admission08_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission08_12_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission08_12_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 12 := by
 rw [admission08_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_12_coefficients]
def admission08_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(62552311962667713/20000000000000000000:ℝ)]]
theorem admission08_13_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (62552311962667713/20000000000000000000:ℝ) admission08_13_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 13 := by
 rw [admission08_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_13_coefficients]
def admission08_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission08_14_identity (δ p : ℝ) : admissionGuard .weakC8 δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission08_14_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC8 δ p 14 := by
 rw [admission08_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_14_coefficients]
theorem admission08_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .weakC8 δ p j := by
 fin_cases j
 · exact admission08_00_pos hδ hp
 · exact admission08_01_pos hδ hp
 · exact admission08_02_pos hδ hp
 · exact admission08_03_pos hδ hp
 · exact admission08_04_pos hδ hp
 · exact admission08_05_pos hδ hp
 · exact admission08_06_pos hδ hp
 · exact admission08_07_pos hδ hp
 · exact admission08_08_pos hδ hp
 · exact admission08_09_pos hδ hp
 · exact admission08_10_pos hδ hp
 · exact admission08_11_pos hδ hp
 · exact admission08_12_pos hδ hp
 · exact admission08_13_pos hδ hp
 · exact admission08_14_pos hδ hp
#print axioms admission08_all
end
end LewkoStage2Return.C30
