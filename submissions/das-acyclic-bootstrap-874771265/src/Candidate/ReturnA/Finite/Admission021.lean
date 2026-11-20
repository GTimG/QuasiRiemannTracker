/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission021_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1029304961169646157824/70916363469:ℝ),(3068716813550866137088/70916363469:ℝ),(3049518743592793800704/70916363469:ℝ),(1010106891211573821440/70916363469:ℝ)],
![(2058609922339292315648/70916363469:ℝ),(6137433627101732274176/70916363469:ℝ),(6099037487185587601408/70916363469:ℝ),(2020213782423147642880/70916363469:ℝ)],
![(1029304961169646157824/70916363469:ℝ),(3068716813550866137088/70916363469:ℝ),(3049518743592793800704/70916363469:ℝ),(1010106891211573821440/70916363469:ℝ)]]
theorem admission021_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission021_00_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission021_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_00_coefficients]
def admission021_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(750103454473259057152/70916363469:ℝ),(2239572945179777171456/70916363469:ℝ),(2228835526939777171456/70916363469:ℝ),(246455345411086352384/23638787823:ℝ)],
![(1500206908946518114304/70916363469:ℝ),(4479145890359554342912/70916363469:ℝ),(4457671053879554342912/70916363469:ℝ),(492910690822172704768/23638787823:ℝ)],
![(750103454473259057152/70916363469:ℝ),(2239572945179777171456/70916363469:ℝ),(2228835526939777171456/70916363469:ℝ),(246455345411086352384/23638787823:ℝ)]]
theorem admission021_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission021_01_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission021_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_01_coefficients]
def admission021_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(79432766713823764676608/14774242389375:ℝ),(711664972405658328498176/44322727168125:ℝ),(141687008877380554981376/8864545433625:ℝ),(235068372122715740438528/44322727168125:ℝ)],
![(158865533427647529353216/14774242389375:ℝ),(1423329944811316656996352/44322727168125:ℝ),(283374017754761109962752/8864545433625:ℝ),(470136744245431480877056/44322727168125:ℝ)],
![(79432766713823764676608/14774242389375:ℝ),(711664972405658328498176/44322727168125:ℝ),(141687008877380554981376/8864545433625:ℝ),(235068372122715740438528/44322727168125:ℝ)]]
theorem admission021_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission021_02_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission021_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_02_coefficients]
def admission021_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1692097495051383341056/212749090407:ℝ),(5031263083580429959168/212749090407:ℝ),(4986351646806709895168/212749090407:ℝ),(1647186058277663277056/212749090407:ℝ)],
![(3339088093072741892096/212749090407:ℝ),(9927279620403822067712/212749090407:ℝ),(9837533840309418459136/212749090407:ℝ),(3249342312978338283520/212749090407:ℝ)],
![(1646990598021358551040/212749090407:ℝ),(4896016536823392108544/212749090407:ℝ),(4851182193502708563968/212749090407:ℝ),(1602156254700675006464/212749090407:ℝ)]]
theorem admission021_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (11936994304513/24206118730752:ℝ) admission021_03_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission021_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_03_coefficients]
def admission021_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3838978974931237756928/2954848477875:ℝ),(11350112707634704965632/2954848477875:ℝ),(11184077047120900653056/2954848477875:ℝ),(3672943314417433444352/2954848477875:ℝ)],
![(7865756007096192293888/2954848477875:ℝ),(5537964043224186919936/703535351875:ℝ),(38205377948335218884608/4924747463125:ℝ),(37647668972778692804608/14774242389375:ℝ)],
![(268451802144330302464/196989898525:ℝ),(59546681369534400490496/14774242389375:ℝ),(8385106944200164769792/2110606055625:ℝ),(918235828604358361088/703535351875:ℝ)]]
theorem admission021_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656773444607991/8068706243584000:ℝ) admission021_04_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission021_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_04_coefficients]
def admission021_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1523657147413521119744/2110606055625:ℝ),(96148420325005154289152/44322727168125:ℝ),(96300753555680418145792/44322727168125:ℝ),(32149133326359207371264/44322727168125:ℝ)],
![(560269061964156854272/422121211125:ℝ),(176867213815389398493184/44322727168125:ℝ),(177238157327331316616192/44322727168125:ℝ),(59199195018178387821568/44322727168125:ℝ)],
![(425896054135754383872/703535351875:ℝ),(80718793490384244204032/44322727168125:ℝ),(3237496150866035938816/1772909086725:ℝ),(27050061691819180450304/44322727168125:ℝ)]]
theorem admission021_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (7486454076605057529/188853832992686080000:ℝ) admission021_05_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission021_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_05_coefficients]
def admission021_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2123831763526104202815085554343936/1107606145736254496527125:ℝ),(168142763662758652390293318541312/29935301236114986392625:ℝ),(6072557640626016662323172042866688/1107606145736254496527125:ℝ),(395020605834229184059480962236416/221521229147250899305425:ℝ)],
![(21706925388551720440363433884865536/5538030728681272482635625:ℝ),(63606703579797428008916326471128064/5538030728681272482635625:ℝ),(434753485529752654720863852963823616/38766215100768907378449375:ℝ),(28290949244876564717478720971997184/7753243020153781475689875:ℝ)],
![(11087766570921199426288006113145856/5538030728681272482635625:ℝ),(32500292302187077316712062540985344/5538030728681272482635625:ℝ),(222213968107842071539552831463489536/38766215100768907378449375:ℝ),(14465228040678543275396887293722624/7753243020153781475689875:ℝ)]]
theorem admission021_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (23545062889708827975957451/201633545463808818567782400:ℝ) admission021_06_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission021_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_06_coefficients]
def admission021_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(160996866703065311102238452523008/41909421730560980949675:ℝ),(2390004615043660548926101896372224/209547108652804904748375:ℝ),(17519666096745861455541325266944/1552200804835591887025:ℝ),(780134641532357303083169277280256/209547108652804904748375:ℝ)],
![(7802901130372569569378824446321664/1047735543264024523741875:ℝ),(23163229098050247390248640031794176/1047735543264024523741875:ℝ),(848841699211771028945822206918656/38805020120889797175625:ℝ),(43190845205943656918099337150464/5987060247222997278525:ℝ)],
![(3777979462795936791822863133246464/1047735543264024523741875:ℝ),(11213206022831944645618130549933056/1047735543264024523741875:ℝ),(410850046793124492557289075245056/38805020120889797175625:ℝ),(731544940675670689050307522985984/209547108652804904748375:ℝ)]]
theorem admission021_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (348827810609660477185395967/1525875479185580248621056000:ℝ) admission021_07_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission021_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_07_coefficients]
def admission021_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(93652687919001794982439051475974633198/1740100750797234607086181640625:ℝ),(6149818027431282719285076729747237849178/36542115766741926748809814453125:ℝ),(14932081258628175298075663298345253270358/85264936789064495747222900390625:ℝ),(15514288364666869529156527203563678446934/255794810367193487241668701171875:ℝ)],
![(2716610470282728812526937333261022091167/17401007507972346070861816406250:ℝ),(175491256980606940910065891164675342414611/365421157667419267488098144531250:ℝ),(209813555763775633876920763903554982790428/426324683945322478736114501953125:ℝ),(42978074439830454318453044371622657536684/255794810367193487241668701171875:ℝ)],
![(1780083591092710862702546818501275759187/17401007507972346070861816406250:ℝ),(113993076706294113717215123867202963922831/365421157667419267488098144531250:ℝ),(135153149470634757386542447411828716438638/426324683945322478736114501953125:ℝ),(219710288601308678314372137344471832718/2046358482937547897933349609375:ℝ)]]
theorem admission021_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (46826343959500897491219525737987316599/13286534784745188559421440000000000000000:ℝ) admission021_08_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission021_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_08_coefficients]
def admission021_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20202649450800787794717520380201600832/136423898862503193195556640625:ℝ),(35166921572365930059100396504161192064/81854339317501915917333984375:ℝ),(169868717965249033120323469074921930752/409271696587509579586669921875:ℝ),(6071365642346249734647383825066196992/45474632954167731065185546875:ℝ)],
![(165802643234750998635060540083054746216/682119494312515965977783203125:ℝ),(1436071509626828032315313284552552276304/2046358482937547897933349609375:ℝ),(1380124040541494552912213833866846611456/2046358482937547897933349609375:ℝ),(654018982092631619564389315131211776/3031642196944515404345703125:ℝ)],
![(64789395980747059661472938182046742056/682119494312515965977783203125:ℝ),(556898470317679780837803371948522474704/2046358482937547897933349609375:ℝ),(530780450715249387310596488492236957696/2046358482937547897933349609375:ℝ),(3738919089043224558818455901901979648/45474632954167731065185546875:ℝ)]]
theorem admission021_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (342308266208791310926982657034483/63578144966065843692544000000000000:ℝ) admission021_09_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission021_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_09_coefficients]
def admission021_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3514678120553341654555654912/86567826500244140625:ℝ),(10121779068428505927900244736/86567826500244140625:ℝ),(9700696365160716154633524736/86567826500244140625:ℝ),(343734152267839097920992768/9618647388916015625:ℝ)],
![(623073142526875387613133376/9618647388916015625:ℝ),(1779880305760899023156121408/9618647388916015625:ℝ),(1690768305485341191597842688/9618647388916015625:ℝ),(533963864907567556054854656/9618647388916015625:ℝ)],
![(410838889278661180025281636/17313565300048828125:ℝ),(5782061907844299523753388548/86567826500244140625:ℝ),(5402403720423000158166615056/86567826500244140625:ℝ),(186060979691551073282181632/9618647388916015625:ℝ)]]
theorem admission021_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3270603158640546210038349/2581985997946880000000000000:ℝ) admission021_10_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission021_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_10_coefficients]
def admission021_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3301565292940179197262699248377856/1047735543264024523741875:ℝ),(1089186528645657079228423039311872/116415060362669391526875:ℝ),(9701133373245172928352472429232128/1047735543264024523741875:ℝ),(1066673302791479470853121441267712/349245181088008174580625:ℝ)],
![(6395469305321654226127505406647296/1047735543264024523741875:ℝ),(2109534914123749426607811503553536/116415060362669391526875:ℝ),(18786147606413004590201167976726528/1047735543264024523741875:ℝ),(2360305784617491038803188514816/399137349814866485235:ℝ)],
![(618780802476295005772961231653888/209547108652804904748375:ℝ),(340116128492697449126462821413888/38805020120889797175625:ℝ),(363400569326713266473947821899776/41909421730560980949675:ℝ),(998594258748825188099668509196288/349245181088008174580625:ℝ)]]
theorem admission021_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (476166848539745897340616469/2543125798642633747701760000:ℝ) admission021_11_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission021_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_11_coefficients]
def admission021_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1380227158537928704/10986328125:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/10986328125:ℝ)],
![(2760454317075857408/10986328125:ℝ),(2760454317075857408/3662109375:ℝ),(2760454317075857408/3662109375:ℝ),(2760454317075857408/10986328125:ℝ)],
![(1380227158537928704/10986328125:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/10986328125:ℝ)]]
theorem admission021_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission021_12_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission021_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_12_coefficients]
def admission021_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(48571909442793111552/762939453125:ℝ),(145715728328379334656/762939453125:ℝ),(145715728328379334656/762939453125:ℝ),(48571909442793111552/762939453125:ℝ)],
![(97143818885586223104/762939453125:ℝ),(291431456656758669312/762939453125:ℝ),(291431456656758669312/762939453125:ℝ),(97143818885586223104/762939453125:ℝ)],
![(48571909442793111552/762939453125:ℝ),(145715728328379334656/762939453125:ℝ),(145715728328379334656/762939453125:ℝ),(48571909442793111552/762939453125:ℝ)]]
theorem admission021_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission021_13_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission021_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_13_coefficients]
def admission021_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)],
![(137438953472/9:ℝ),(137438953472/3:ℝ),(137438953472/3:ℝ),(137438953472/9:ℝ)],
![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)]]
theorem admission021_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission021_14_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission021_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_14_coefficients]
theorem admission021_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission021_00_pos hd hp
 · exact admission021_01_pos hd hp
 · exact admission021_02_pos hd hp
 · exact admission021_03_pos hd hp
 · exact admission021_04_pos hd hp
 · exact admission021_05_pos hd hp
 · exact admission021_06_pos hd hp
 · exact admission021_07_pos hd hp
 · exact admission021_08_pos hd hp
 · exact admission021_09_pos hd hp
 · exact admission021_10_pos hd hp
 · exact admission021_11_pos hd hp
 · exact admission021_12_pos hd hp
 · exact admission021_13_pos hd hp
 · exact admission021_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission021_all
