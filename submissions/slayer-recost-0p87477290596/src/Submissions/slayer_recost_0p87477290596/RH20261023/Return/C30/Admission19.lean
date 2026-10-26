/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def admission19_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(66368673311749/1066279917429:ℝ), (191907180182960/3198839752287:ℝ)]]
theorem admission19_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission19_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission19_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_00_coefficients]
def admission19_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(48241914715456/1066279917429:ℝ), (140725744146368/3198839752287:ℝ)]]
theorem admission19_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission19_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission19_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_01_coefficients]
def admission19_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(24480055483948/1066279917429:ℝ), (71511986077088/3198839752287:ℝ)]]
theorem admission19_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission19_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission19_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_02_coefficients]
def admission19_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1826142498945438400/9596519256861:ℝ), (10677179781223579712/28789557770583:ℝ), (5200156284387264512/28789557770583:ℝ)],
![(1779327661863723520/9596519256861:ℝ), (10396680227035973120/28789557770583:ℝ), (5060137241444802560/28789557770583:ℝ)]]
theorem admission19_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (617692534356055/1228354464878208:ℝ) admission19_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission19_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_03_coefficients]
def admission19_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32435487226843220/1066279917429:ℝ), (62159407090040000/1066279917429:ℝ), (29748986208068608/1066279917429:ℝ)],
![(3781106767184608/118475546381:ℝ), (195836481232133632/3198839752287:ℝ), (93823725733139456/3198839752287:ℝ)]]
theorem admission19_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (29051744343817/363956878482432:ℝ) admission19_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission19_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_04_coefficients]
def admission19_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4303143408396193424/239912981421525:ℝ), (215849146092192194756/5997824535538125:ℝ), (36067552814127775552/1999274845179375:ℝ)],
![(18259555681095365056/1199564907107625:ℝ), (36739780124704873312/1199564907107625:ℝ), (6155431912662722752/399854969035875:ℝ)]]
theorem admission19_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (285305557517115079/6551223812683776000:ℝ) admission19_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission19_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_05_coefficients]
def admission19_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10119505239566643668666982349273472/3407447728350247988736212877:ℝ), (28995481481183907134315765363886464/3407447728350247988736212877:ℝ), (27658820459168594003924039488458752/3407447728350247988736212877:ℝ), (8782702717157159585003256473845760/3407447728350247988736212877:ℝ)],
![(10558611936111786046465952627287040/3407447728350247988736212877:ℝ), (30290781261918264035285063616128000/3407447728350247988736212877:ℝ), (28932553574234702362787696635904000/3407447728350247988736212877:ℝ), (9200239119818818268048585647063040/3407447728350247988736212877:ℝ)]]
theorem admission19_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (67006704079873348884607364455/581537745638442323410980331008:ℝ) admission19_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission19_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_06_coefficients]
def admission19_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8694749637531334163833725894236/92093181847303999695573321:ℝ), (5623347210120550437011416915136/30697727282434666565191107:ℝ), (8179303504012883984044396206080/92093181847303999695573321:ℝ)],
![(8184645792312092786866238709920/92093181847303999695573321:ℝ), (5288670273864019453461810475520/30697727282434666565191107:ℝ), (7685251614508750052122251468800/92093181847303999695573321:ℝ)]]
theorem admission19_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (938141066224212652846954525/3929309092151637320344461696:ℝ) admission19_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission19_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_07_coefficients]
def admission19_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(527759945995307753371970918649096786901888349363/11511647730912999961946665125000000000000000:ℝ), (9348633367158779106909135112936676824958902494721/57558238654564999809733325625000000000000000:ℝ), (10776856577757381413217288328637833387768932053251/57558238654564999809733325625000000000000000:ℝ), (813315677587291166048764110537803087438894261069/11511647730912999961946665125000000000000000:ℝ)],
![(1377004685020538363626931511275894059998405616349/11511647730912999961946665125000000000000000:ℝ), (871303991914845796835676423102761291488919551051/2302329546182599992389333025000000000000000:ℝ), (4582181609762694665617238602689819381226865100263/11511647730912999961946665125000000000000000:ℝ), (1602575144924145533696723945886240304780672961357/11511647730912999961946665125000000000000000:ℝ)]]
theorem admission19_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (527759945995307753371970918649096786901888349363/257511200663249703426094641709056000000000000000000:ℝ) admission19_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission19_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_08_coefficients]
def admission19_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(675206994438850464276063792584349015923/2398259943940208325405555234375000:ℝ), (9543545830838492106260563589931184742623/11991299719701041627027776171875000:ℝ), (1120472658510106666659107333044166710136/1498912464962630203378472021484375:ℝ), (69908685212809243727632894390277037952/299782492992526040675694404296875:ℝ)],
![(60163943670444644103904216705742320057/299782492992526040675694404296875:ℝ), (167509792072683242932987456955888903449/299782492992526040675694404296875:ℝ), (154623105304026300320616922627275353152/299782492992526040675694404296875:ℝ), (9455846247412700301961617184488253952/59956498598505208135138880859375:ℝ)]]
theorem admission19_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (18468449701977930277268783563453621/2619539394767758213562974464000000000:ℝ) admission19_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission19_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_09_coefficients]
def admission19_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(633236967702741005826742736/93716008367783203125:ℝ), (985316090776236781901330624/52064449093212890625:ℝ), (8240857392149632047360310192/468580041838916015625:ℝ), (2539258016020956039382048256/468580041838916015625:ℝ)],
![(3234508094111501451027102976/281148025103349609375:ℝ), (2992650245698280626359784448/93716008367783203125:ℝ), (1651276597621550318735479552/56229605020669921875:ℝ), (279223881402712351736127488/31238669455927734375:ℝ)],
![(263684557341516747956489216/56229605020669921875:ℝ), (240611429138094053625327616/18743201673556640625:ℝ), (652966731782878897882498048/56229605020669921875:ℝ), (64941550570037828321001472/18743201673556640625:ℝ)]]
theorem admission19_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3963717686159535419983/2183741270894592000000000:ℝ) admission19_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission19_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_10_coefficients]
def admission19_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7139589358666120279929047552228/92093181847303999695573321:ℝ), (4618014462282842944142746625792/30697727282434666565191107:ℝ), (6718304262255473536126446694400/92093181847303999695573321:ℝ)],
![(6710976532015041149019808995680/92093181847303999695573321:ℝ), (4336887218552222038788052428800/30697727282434666565191107:ℝ), (6303406296450407545212415262720/92093181847303999695573321:ℝ)]]
theorem admission19_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (384729388211084444898218705/1964654546075818660172230848:ℝ) admission19_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission19_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_11_coefficients]
def admission19_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission19_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission19_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission19_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_12_coefficients]
def admission19_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission19_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission19_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission19_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_13_coefficients]
def admission19_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission19_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission19_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission19_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_14_coefficients]
theorem admission19_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission19_00_pos hδ hp
 · exact admission19_01_pos hδ hp
 · exact admission19_02_pos hδ hp
 · exact admission19_03_pos hδ hp
 · exact admission19_04_pos hδ hp
 · exact admission19_05_pos hδ hp
 · exact admission19_06_pos hδ hp
 · exact admission19_07_pos hδ hp
 · exact admission19_08_pos hδ hp
 · exact admission19_09_pos hδ hp
 · exact admission19_10_pos hδ hp
 · exact admission19_11_pos hδ hp
 · exact admission19_12_pos hδ hp
 · exact admission19_13_pos hδ hp
 · exact admission19_14_pos hδ hp
#print axioms admission19_all
end
end RH20261023Return.C30
