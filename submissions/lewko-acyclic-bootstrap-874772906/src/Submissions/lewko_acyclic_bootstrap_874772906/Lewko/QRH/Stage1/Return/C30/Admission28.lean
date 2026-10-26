/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission28_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(66368673311749/1066279917429:ℝ), (191907180182960/3198839752287:ℝ)]]
theorem admission28_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission28_00_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission28_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_00_coefficients]
def admission28_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(48241914715456/1066279917429:ℝ), (140725744146368/3198839752287:ℝ)]]
theorem admission28_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission28_01_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission28_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_01_coefficients]
def admission28_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(24480055483948/1066279917429:ℝ), (71511986077088/3198839752287:ℝ)]]
theorem admission28_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission28_02_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission28_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_02_coefficients]
def admission28_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1802664169020800512/9596519256861:ℝ), (10536699269978435072/28789557770583:ℝ), (5130146762916033536/28789557770583:ℝ)],
![(1755849331939085632/9596519256861:ℝ), (10256199715790828480/28789557770583:ℝ), (4990127719973571584/28789557770583:ℝ)]]
theorem admission28_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (4873171601536691/9826835719025664:ℝ) admission28_03_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission28_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_03_coefficients]
def admission28_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(99801499159517600/3198839752287:ℝ), (191259714123200000/3198839752287:ℝ), (91535342178672640/3198839752287:ℝ)],
![(104584920192972356/3198839752287:ℝ), (66872658028404544/1066279917429:ℝ), (32037369762535424/1066279917429:ℝ)]]
theorem admission28_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (11173747824545/136483829430912:ℝ) admission28_04_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission28_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_04_coefficients]
def admission28_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19887636361538166088/1199564907107625:ℝ), (39995941485590475376/1199564907107625:ℝ), (6698125472810323096/399854969035875:ℝ)],
![(16631475000652564024/1199564907107625:ℝ), (167829461959284548684/5997824535538125:ℝ), (3133359345915272632/222141649464375:ℝ)]]
theorem admission28_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2078934375081570503/52409790501470208000:ℝ) admission28_05_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission28_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_05_coefficients]
def admission28_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10349843734780956704943288040678400/3407447728350247988736212877:ℝ), (29664476657925776010717069856302080/3407447728350247988736212877:ℝ), (28306248970242214338219702876078080/3407447728350247988736212877:ℝ), (8991470918487988926525921060454400/3407447728350247988736212877:ℝ)],
![(10788950431326099082742258318691968/3407447728350247988736212877:ℝ), (30959776438660132911686368108543616/3407447728350247988736212877:ℝ), (29579982085308322697083360023523328/3407447728350247988736212877:ℝ), (9409007321149647609571250233671680/3407447728350247988736212877:ℝ)]]
theorem admission28_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (8574934881675709654355927525/72692218204805290426372541376:ℝ) admission28_06_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission28_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_06_coefficients]
def admission28_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8431671737064159752827311078560/92093181847303999695573321:ℝ), (5453354237032064097435858721280/30697727282434666565191107:ℝ), (7932277559260817018083323837440/92093181847303999695573321:ℝ)],
![(7921567891844918375859823894244/92093181847303999695573321:ℝ), (5118677300775533113886252281664/30697727282434666565191107:ℝ), (7438225669756683086161179100160/92093181847303999695573321:ℝ)]]
theorem admission28_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (7263892255621760826329276465/31434472737213098562755693568:ℝ) admission28_07_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission28_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_07_coefficients]
def admission28_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(119047789438490382312431401870311927931268372857/1438955966364124995243333140625000000000000:ℝ), (385331606379547883599492653321701318474977731847/1438955966364124995243333140625000000000000:ℝ), (413539312653106093779349714218702933947761149973/1438955966364124995243333140625000000000000:ℝ), (147244096926441278571155456196605208529051790983/1438955966364124995243333140625000000000000:ℝ)],
![(900813527266576834377205903794646348273332124921/5755823865456499980973332562500000000000000:ℝ), (13923615342947140578981240798750204100631597777717/28779119327282499904866662812500000000000000:ℝ), (3584452997147541958255361656694922609534479930873/7194779831820624976216665703125000000000000:ℝ), (245901530343548074527150435615159860696774128519/1438955966364124995243333140625000000000000:ℝ)]]
theorem admission28_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (119047789438490382312431401870311927931268372857/32188900082906212928261830213632000000000000000000:ℝ) admission28_08_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission28_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_08_coefficients]
def admission28_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(71478670658317515212816620939660204153/299782492992526040675694404296875:ℝ), (201453973036301856259724669657642555737/299782492992526040675694404296875:ℝ), (37713457253528982729470827065805801088/59956498598505208135138880859375:ℝ), (58593958224936372618720490156359153856/299782492992526040675694404296875:ℝ)],
![(377933920191246810257702908578871177757/2398259943940208325405555234375000:ℝ), (5215004773520911861447921474610073624817/11991299719701041627027776171875000:ℝ), (595479299348249403180747956737355082824/1498912464962630203378472021484375:ℝ), (35964504249190630400895681688523385664/299782492992526040675694404296875:ℝ)]]
theorem admission28_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (561945378893603600013995026383177901/104781575790710328542518978560000000000:ℝ) admission28_09_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission28_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_09_coefficients]
def admission28_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8042377133499284781852229376/1405740125516748046875:ℝ), (7465548928413717423573189376/468580041838916015625:ℝ), (20674957894456070695882448128/1405740125516748046875:ℝ), (234106647878303822482041088/52064449093212890625:ℝ)],
![(4365480554505633235464468224/468580041838916015625:ℝ), (444385855008916088763475456/17354816364404296875:ℝ), (3635148604168592035278089984/156193347279638671875:ℝ), (3272638969270674944684900864/468580041838916015625:ℝ)],
![(4972192508539141455719031856/1405740125516748046875:ℝ), (4452748473774096218986891712/468580041838916015625:ℝ), (11806205073543368242376754704/1405740125516748046875:ℝ), (1140117697597157013711703808/468580041838916015625:ℝ)]]
theorem admission28_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4453584756238894584811343/3493986033431347200000000000:ℝ) admission28_10_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission28_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_10_coefficients]
def admission28_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6918425514917574144476824711520/92093181847303999695573321:ℝ), (4475186540487244035759396239360/30697727282434666565191107:ℝ), (6510855279352940540669430978560/92093181847303999695573321:ℝ)],
![(6489812688266495013567586154972/92093181847303999695573321:ℝ), (4194059296756623130404702042368/30697727282434666565191107:ℝ), (6095957313547874549755399546880/92093181847303999695573321:ℝ)]]
theorem admission28_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2976541657005798119997753685/15717236368606549281377846784:ℝ) admission28_11_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission28_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_11_coefficients]
def admission28_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission28_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission28_12_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission28_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_12_coefficients]
def admission28_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission28_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission28_13_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission28_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_13_coefficients]
def admission28_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission28_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission28_14_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission28_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_14_coefficients]
theorem admission28_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission28_00_pos hδ hp
 · exact admission28_01_pos hδ hp
 · exact admission28_02_pos hδ hp
 · exact admission28_03_pos hδ hp
 · exact admission28_04_pos hδ hp
 · exact admission28_05_pos hδ hp
 · exact admission28_06_pos hδ hp
 · exact admission28_07_pos hδ hp
 · exact admission28_08_pos hδ hp
 · exact admission28_09_pos hδ hp
 · exact admission28_10_pos hδ hp
 · exact admission28_11_pos hδ hp
 · exact admission28_12_pos hδ hp
 · exact admission28_13_pos hδ hp
 · exact admission28_14_pos hδ hp
#print axioms admission28_all
end
end LewkoStage1Return.C30
