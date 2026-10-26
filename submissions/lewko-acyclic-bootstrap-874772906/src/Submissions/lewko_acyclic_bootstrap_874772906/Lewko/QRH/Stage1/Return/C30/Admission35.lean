/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission35_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(86091951164903/355426639143:ℝ), (767628720731840/3198839752287:ℝ)]]
theorem admission35_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission35_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission35_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_00_coefficients]
def admission35_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(62989219620608/355426639143:ℝ), (562902976585472/3198839752287:ℝ)]]
theorem admission35_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission35_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission35_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_01_coefficients]
def admission35_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31997347187012/355426639143:ℝ), (286047944308352/3198839752287:ℝ)]]
theorem admission35_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission35_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission35_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_02_coefficients]
def admission35_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1374012496170167296/118475546381:ℝ), (663328965739516494848/28789557770583:ℝ), (329449545170165841920/28789557770583:ℝ)],
![(36849213556562281216/3198839752287:ℝ), (658846510492146981632/28789557770583:ℝ), (327209240483086450688/28789557770583:ℝ)]]
theorem admission35_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (19971267119329007/39307342876102656:ℝ) admission35_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission35_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_03_coefficients]
def admission35_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1946618337478322768/1066279917429:ℝ), (3850453189415226368/1066279917429:ℝ), (1903935117316390912/1066279917429:ℝ)],
![(1971301372444955548/1066279917429:ℝ), (11698635018708140800/3198839752287:ℝ), (5785033625692110848/3198839752287:ℝ)]]
theorem admission35_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (29051744343817/363956878482432:ℝ) admission35_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission35_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_04_coefficients]
def admission35_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(260288595536093122406/239912981421525:ℝ), (13023871729005079717196/5997824535538125:ℝ), (2172128410281045175682/1999274845179375:ℝ)],
![(6251642727419914196858/5997824535538125:ℝ), (12514362433071788755388/5997824535538125:ℝ), (139165474551201239134/133284989678625:ℝ)]]
theorem admission35_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (3125821363709957098429/67084531841881866240000:ℝ) admission35_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission35_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_05_coefficients]
def admission35_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(63045222397716650800218222554691584/92093181847303999695573321:ℝ), (6913302041591020479247166833415591936/3407447728350247988736212877:ℝ), (6829001274469313937213014256196517888/3407447728350247988736212877:ℝ), (2248371895592232853760833657304514560/3407447728350247988736212877:ℝ)],
![(2359735315661724052360777901562200576/3407447728350247988736212877:ℝ), (6994146766963003645232667348670710272/3407447728350247988736212877:ℝ), (6909506246293650521313360171498930176/3407447728350247988736212877:ℝ), (2275094225362579009475734724390420480/3407447728350247988736212877:ℝ)]]
theorem admission35_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (67006704079873348884607364455/581537745638442323410980331008:ℝ) admission35_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission35_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_06_coefficients]
def admission35_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(519817178910829761447212702246000/92093181847303999695573321:ℝ), (114602145752758317190283011146752/10232575760811555521730369:ℝ), (511618178908725360612709883494400/92093181847303999695573321:ℝ)],
![(511848515633764535830999454469620/92093181847303999695573321:ℝ), (112838438132405252060424483261184/10232575760811555521730369:ℝ), (503713348676659217701955567697920/92093181847303999695573321:ℝ)]]
theorem admission35_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (30744222941690626080441624005/125737890948852394251022774272:ℝ) admission35_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission35_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_07_coefficients]
def admission35_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(50794651028006512162769587972513800439020191843839/3597389915910312488108332851562500000000000:ℝ), (31617164652568339864752055313121784299043169674829/719477983182062497621666570312500000000000:ℝ), (163782682231596259862610949769597716829469323521027/3597389915910312488108332851562500000000000:ℝ), (56491398858601401390889214362438189508242416990721/3597389915910312488108332851562500000000000:ℝ)],
![(133752378845668451495478907106574031972878322531559/7194779831820624976216665703125000000000000:ℝ), (412065798199445527115355943803987323447229982502699/7194779831820624976216665703125000000000000:ℝ), (211433409732810798321638047045088655128214758482051/3597389915910312488108332851562500000000000:ℝ), (72276588205338488743848411069406933855077990996481/3597389915910312488108332851562500000000000:ℝ)]]
theorem admission35_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (50794651028006512162769587972513800439020191843839/20600896053059976274087571336724480000000000000000000:ℝ) admission35_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission35_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_08_coefficients]
def admission35_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(83228904045277739668174723762136082980558/1498912464962630203378472021484375:ℝ), (245068813213241321869814758841417269438142/1498912464962630203378472021484375:ℝ), (240460849832463579808097880965141032553984/1498912464962630203378472021484375:ℝ), (3144839166561515028272567870199737593856/59956498598505208135138880859375:ℝ)],
![(151720692223992087535516503722171555027677/2997824929925260406756944042968750:ℝ), (446181519649227271832748568670302363294213/2997824929925260406756944042968750:ℝ), (218609928858087042770367655349774640345728/1498912464962630203378472021484375:ℝ), (14275910778359847639422051609057198804992/299782492992526040675694404296875:ℝ)]]
theorem admission35_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3485329779873009677593274318617480177/419126303162841314170075914240000000000:ℝ) admission35_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission35_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_09_coefficients]
def admission35_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(481173669005733281618081589248/93716008367783203125:ℝ), (2352532961858773856881199163392/156193347279638671875:ℝ), (6897839688322126960890371141632/468580041838916015625:ℝ), (2246110117411971798337181597696/468580041838916015625:ℝ)],
![(13741816623723265915486596482048/1405740125516748046875:ℝ), (1491674137901881146814179447808/52064449093212890625:ℝ), (39326398750131663654028700735488/1405740125516748046875:ℝ), (284289322347175302345165602816/31238669455927734375:ℝ)],
![(6519221583540379460727453222272/1405740125516748046875:ℝ), (2120835280483075110513764104832/156193347279638671875:ℝ), (3723614870248176411383888844032/281148025103349609375:ℝ), (2016593785586455591007673499648/468580041838916015625:ℝ)]]
theorem admission35_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (123083116796048314880839447/55903776534901555200000000000:ℝ) admission35_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission35_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_10_coefficients]
def admission35_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(426708280338722290627470395375504/92093181847303999695573321:ℝ), (94078533445273194802568579108864/10232575760811555521730369:ℝ), (420013921605028722530155834081280/92093181847303999695573321:ℝ)],
![(420015440626250029430142626160908/92093181847303999695573321:ℝ), (92597302544818857619658236361728/10232575760811555521730369:ℝ), (413375554152147666675531331174400/92093181847303999695573321:ℝ)]]
theorem admission35_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12615220768803334554306986425/62868945474426197125511387136:ℝ) admission35_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission35_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_11_coefficients]
def admission35_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission35_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission35_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission35_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_12_coefficients]
def admission35_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission35_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission35_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission35_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_13_coefficients]
def admission35_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission35_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission35_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission35_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_14_coefficients]
theorem admission35_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission35_00_pos hδ hp
 · exact admission35_01_pos hδ hp
 · exact admission35_02_pos hδ hp
 · exact admission35_03_pos hδ hp
 · exact admission35_04_pos hδ hp
 · exact admission35_05_pos hδ hp
 · exact admission35_06_pos hδ hp
 · exact admission35_07_pos hδ hp
 · exact admission35_08_pos hδ hp
 · exact admission35_09_pos hδ hp
 · exact admission35_10_pos hδ hp
 · exact admission35_11_pos hδ hp
 · exact admission35_12_pos hδ hp
 · exact admission35_13_pos hδ hp
 · exact admission35_14_pos hδ hp
#print axioms admission35_all
end
end LewkoStage1Return.C30
