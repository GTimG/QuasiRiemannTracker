/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(391013200118207/3198839752287:ℝ), (383814360365920/3198839752287:ℝ)]]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission16_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission16_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]
def admission16_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(285451488292736/3198839752287:ℝ), (281451488292736/3198839752287:ℝ)]]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission16_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission16_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]
def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(144952152528932/3198839752287:ℝ), (143023972154176/3198839752287:ℝ)]]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission16_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission16_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]
def admission16_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(42712414061499684224/28789557770583:ℝ), (9367876926288644480/3198839752287:ℝ), (41601250275098116096/28789557770583:ℝ)],
![(42151450953124471040/28789557770583:ℝ), (9243313006272526592/3198839752287:ℝ), (41041174103328268288/28789557770583:ℝ)]]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (5009908948160189/9826835719025664:ℝ) admission16_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission16_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]
def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(736498369263176212/3198839752287:ℝ), (1441172034150099328/3198839752287:ℝ), (704822134775779328/3198839752287:ℝ)],
![(755216817367578232/3198839752287:ℝ), (1478195622509861120/3198839752287:ℝ), (723129203211513856/3198839752287:ℝ)]]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (172075716497993/2183741270894592:ℝ) admission16_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission16_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]
def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(95680415043547331336/666424948393125:ℝ), (1723924509609794878384/5997824535538125:ℝ), (172533342085252699772/1199564907107625:ℝ)],
![(88535722596265295348/666424948393125:ℝ), (1596139299662689280488/5997824535538125:ℝ), (799181991416493557356/5997824535538125:ℝ)]]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (22133930649066323837/465864804457512960000:ℝ) admission16_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission16_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]
def admission16_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(149357489409791977195324149192880384/3407447728350247988736212877:ℝ), (145821536199402366816524401664801536/1135815909450082662912070959:ℝ), (426960496424856148636015842690187264/3407447728350247988736212877:ℝ), (138853097863867918627870786888663040/3407447728350247988736212877:ℝ)],
![(152783165404799243516001404043798016/3407447728350247988736212877:ℝ), (149218453011970066595079468375990784/1135815909450082662912070959:ℝ), (437065865717060486268014421358575616/3407447728350247988736212877:ℝ), (142193389085161188092233420274401280/3407447728350247988736212877:ℝ)]]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (132420633186214369418974673165/1163075491276884646821960662016:ℝ) admission16_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission16_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]
def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(67520168529288171449674617982772/92093181847303999695573321:ℝ), (132946448613072327290101232318848/92093181847303999695573321:ℝ), (65434428032103071872355169648640/92093181847303999695573321:ℝ)],
![(65511981985795203190136166742328/92093181847303999695573321:ℝ), (128962179437516605661115014732032/92093181847303999695573321:ℝ), (63458220474086536144666590699520/92093181847303999695573321:ℝ)]]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (7746364803965641619221995935/31434472737213098562755693568:ℝ) admission16_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission16_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]
def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(194820965653407555203245643140820897185782727109/355297769472623455615637812500000000000000:ℝ), (5961433428416372019995353716305497275235578509843/3197679925253611100540740312500000000000000:ℝ), (59950178869708075246866214471416011652506635208449/28779119327282499904866662812500000000000000:ℝ), (22077337378640857452407307366100757954747329515691/28779119327282499904866662812500000000000000:ℝ)],
![(397046514626116707168469607889708498622949144183/355297769472623455615637812500000000000000:ℝ), (11354873582069412593155351756803435137360195585621/3197679925253611100540740312500000000000000:ℝ), (107896065831925890106042818901491655209490783113217/28779119327282499904866662812500000000000000:ℝ), (37862526725377944805366504073069502301582903521451/28779119327282499904866662812500000000000000:ℝ)]]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (194820965653407555203245643140820897185782727109/127166025018888742432639329239040000000000000000000:ℝ) admission16_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission16_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]
def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(24807330137635278732830282490145337693029/5995649859850520813513888085937500:ℝ), (23991522004525637957221651424247194827879/1998549953283506937837962695312500:ℝ), (17384484783033118707743408362747591921312/1498912464962630203378472021484375:ℝ), (1118538963404947899642126310244432607232/299782492992526040675694404296875:ℝ)],
![(10529498421753324377583543818981811055343/2997824929925260406756944042968750:ℝ), (10143027212786109962614758071063504097653/999274976641753468918981347656250:ℝ), (14637289016528473514449828975046286052288/1498912464962630203378472021484375:ℝ), (937503331598981961899527842501746461696/299782492992526040675694404296875:ℝ)]]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (915530597264630822167507658693111779/104781575790710328542518978560000000000:ℝ) admission16_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission16_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]
def admission16_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6069606601361847715030112896/31238669455927734375:ℝ), (788091684779936391460654230208/1405740125516748046875:ℝ), (756887024820531360003268219456/1405740125516748046875:ℝ), (80642781934219788572989689856/468580041838916015625:ℝ)],
![(18651170614919600622340985344/52064449093212890625:ℝ), (1449325648019640407301458215168/1405740125516748046875:ℝ), (1388098671441597644779996617472/1405740125516748046875:ℝ), (147452021944720484760581668864/468580041838916015625:ℝ)],
![(5107004815090768754016000512/31238669455927734375:ℝ), (219784145109825610094693376256/468580041838916015625:ℝ), (209783578958439506742966729472/468580041838916015625:ℝ), (22201582828116809319504453632/156193347279638671875:ℝ)]]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2710154153822852700134821/1164662011143782400000000000:ℝ) admission16_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission16_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]
def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(55451174675967989171198695100492/92093181847303999695573321:ℝ), (109189779244601365087196572519936/92093181847303999695573321:ℝ), (53746434098043788289011573555200/92093181847303999695573321:ℝ)],
![(53764282152319981333311342521288/92093181847303999695573321:ℝ), (105843423918997375691412281611264/92093181847303999695573321:ℝ), (52086842234823524325355447828480/92093181847303999695573321:ℝ)]]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3179128554371552998373745595/15717236368606549281377846784:ℝ) admission16_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission16_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]
def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission16_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission16_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]
def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission16_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission16_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]
def admission16_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission16_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission16_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]
theorem admission16_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission16_00_pos hδ hp
 · exact admission16_01_pos hδ hp
 · exact admission16_02_pos hδ hp
 · exact admission16_03_pos hδ hp
 · exact admission16_04_pos hδ hp
 · exact admission16_05_pos hδ hp
 · exact admission16_06_pos hδ hp
 · exact admission16_07_pos hδ hp
 · exact admission16_08_pos hδ hp
 · exact admission16_09_pos hδ hp
 · exact admission16_10_pos hδ hp
 · exact admission16_11_pos hδ hp
 · exact admission16_12_pos hδ hp
 · exact admission16_13_pos hδ hp
 · exact admission16_14_pos hδ hp
#print axioms admission16_all
end
end RH20261023Return.C30
