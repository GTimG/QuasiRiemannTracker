/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission006_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4117219844678584631296/70916363469:ℝ),(12274867254203464548352/70916363469:ℝ),(12198074974371175202816/70916363469:ℝ),(4040427564846295285760/70916363469:ℝ)],
![(8234439689357169262592/70916363469:ℝ),(24549734508406929096704/70916363469:ℝ),(24396149948742350405632/70916363469:ℝ),(8080855129692590571520/70916363469:ℝ)],
![(4117219844678584631296/70916363469:ℝ),(12274867254203464548352/70916363469:ℝ),(12198074974371175202816/70916363469:ℝ),(4040427564846295285760/70916363469:ℝ)]]
theorem admission006_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission006_00_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission006_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_00_coefficients]
def admission006_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3000413817893036228608/70916363469:ℝ),(8958291780719108685824/70916363469:ℝ),(8915342107759108685824/70916363469:ℝ),(985821381644345409536/23638787823:ℝ)],
![(6000827635786072457216/70916363469:ℝ),(17916583561438217371648/70916363469:ℝ),(17830684215518217371648/70916363469:ℝ),(1971642763288690819072/23638787823:ℝ)],
![(3000413817893036228608/70916363469:ℝ),(8958291780719108685824/70916363469:ℝ),(8915342107759108685824/70916363469:ℝ),(985821381644345409536/23638787823:ℝ)]]
theorem admission006_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission006_01_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission006_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_01_coefficients]
def admission006_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(317731066855295058706432/14774242389375:ℝ),(2846659889622633313992704/44322727168125:ℝ),(566748035509522219925504/8864545433625:ℝ),(940273488490862961754112/44322727168125:ℝ)],
![(635462133710590117412864/14774242389375:ℝ),(5693319779245266627985408/44322727168125:ℝ),(1133496071019044439851008/8864545433625:ℝ),(1880546976981725923508224/44322727168125:ℝ)],
![(317731066855295058706432/14774242389375:ℝ),(2846659889622633313992704/44322727168125:ℝ),(566748035509522219925504/8864545433625:ℝ),(940273488490862961754112/44322727168125:ℝ)]]
theorem admission006_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission006_02_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission006_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_02_coefficients]
def admission006_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6904096138560790331392/212749090407:ℝ),(20531577654723198582784/212749090407:ℝ),(20351315160004026171392/212749090407:ℝ),(6723833643841617920000/212749090407:ℝ)],
![(13717978483061531082752/212749090407:ℝ),(40792662215932321464320/212749090407:ℝ),(5776041630485721382912/30392727201:ℝ),(1908229668647037042688/30392727201:ℝ)],
![(6813882344500740751360/212749090407:ℝ),(20261084561209122881536/212749090407:ℝ),(20080976253396023508992/212749090407:ℝ),(6633774036687641378816/212749090407:ℝ)]]
theorem admission006_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (24712734061061/48412237461504:ℝ) admission006_03_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission006_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_03_coefficients]
def admission006_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(72940600523693517381632/14774242389375:ℝ),(215652141445059394347008/14774242389375:ℝ),(212497463895297112408064/14774242389375:ℝ),(69785922973931235442688/14774242389375:ℝ)],
![(147759181619724202563584/14774242389375:ℝ),(145632172850946846672896/4924747463125:ℝ),(20502174025627977383936/703535351875:ℝ),(20201188229295883943936/2110606055625:ℝ)],
![(24939527032010228393984/4924747463125:ℝ),(44248875421556229134336/2954848477875:ℝ),(218048190642890412654592/14774242389375:ℝ),(23874131543713317388288/4924747463125:ℝ)]]
theorem admission006_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478695447551829/161374124871680000:ℝ) admission006_04_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission006_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_04_coefficients]
def admission006_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1366507108934571676672/422121211125:ℝ),(430550465700016637877248/44322727168125:ℝ),(430629582217986570025984/44322727168125:ℝ),(143562362956099958199296/44322727168125:ℝ)],
![(4391044373111066943488/703535351875:ℝ),(830241677730791455584256/44322727168125:ℝ),(830532464867914100701184/44322727168125:ℝ),(276926582643119862556672/44322727168125:ℝ)],
![(6340597574660342447104/2110606055625:ℝ),(57098744575824973958144/6331818166875:ℝ),(2285159329428157318144/253272726675:ℝ),(19052031383859986336768/6331818166875:ℝ)]]
theorem admission006_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (18575969457012722013/377707665985372160000:ℝ) admission006_05_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission006_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_05_coefficients]
def admission006_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(283884549438987033976508662797246464/38766215100768907378449375:ℝ),(831292588585624438408185884763693056/38766215100768907378449375:ℝ),(811132874389021735858212823222976512/38766215100768907378449375:ℝ),(52744857470869998435067120251305984/7753243020153781475689875:ℝ)],
![(574329607424043565723993422374459392/38766215100768907378449375:ℝ),(1682099511515323049559480950079182848/38766215100768907378449375:ℝ),(1641614650149906448432909266372263936/38766215100768907378449375:ℝ),(106768728614701040536764347733508096/7753243020153781475689875:ℝ)],
![(290445057985056531747484759577212928/38766215100768907378449375:ℝ),(850806922929698611151295065315489792/38766215100768907378449375:ℝ),(830481775760884712574696443149287424/38766215100768907378449375:ℝ),(54023871143831042101697227482202112/7753243020153781475689875:ℝ)]]
theorem admission006_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3143838493279814626876540199/28228696364933234599489536000:ℝ) admission006_06_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission006_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_06_coefficients]
def admission006_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16860481787134933645267086833573888/1047735543264024523741875:ℝ),(50050401155712579718156437810798592/1047735543264024523741875:ℝ),(1834128063410188568335024549527552/38805020120889797175625:ℝ),(653261533739897810886252474400768/41909421730560980949675:ℝ)],
![(33227079164708475319067977307490304/1047735543264024523741875:ℝ),(98627168206652443238288117757741056/1047735543264024523741875:ℝ),(3613972915569333049007560986198016/38805020120889797175625:ℝ),(6435435935685604880796801235419136/209547108652804904748375:ℝ)],
![(16366597377573541673800890473916416/1047735543264024523741875:ℝ),(48576767050939863520131679946942464/1047735543264024523741875:ℝ),(1779844852159144480672536436670464/38805020120889797175625:ℝ),(3169128266986115826365538863415296/209547108652804904748375:ℝ)]]
theorem admission006_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (755579058405426937667259899/3051750958371160497242112000:ℝ) admission006_07_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission006_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_07_coefficients]
def admission006_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(185940334574650073892468422036433809546/8700503753986173035430908203125:ℝ),(19304920520439815310891802587455123087438/182710578833709633744049072265625:ℝ),(62705353052004175178378171906095116311234/426324683945322478736114501953125:ℝ),(11473076024694356651958414113067313546414/182710578833709633744049072265625:ℝ)],
![(1215437381051993060663093147814397046299/8700503753986173035430908203125:ℝ),(91104737472860917146147961744640831605927/182710578833709633744049072265625:ℝ),(246396192458996112149084605652395132796164/426324683945322478736114501953125:ℝ),(280118041450688145728817697227895396077956/1278974051835967436208343505859375:ℝ)],
![(1029497046477342986770624725777963236753/8700503753986173035430908203125:ℝ),(71799816952421101835256159157185708518489/182710578833709633744049072265625:ℝ),(36738167881398387394141286749260003296986/85264936789064495747222900390625:ℝ),(199806509277827649165108798436424201253058/1278974051835967436208343505859375:ℝ)]]
theorem admission006_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (92970167287325036946234211018216904773/265730695694903771188428800000000000000000:ℝ) admission006_08_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission006_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_08_coefficients]
def admission006_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(518910307704343902204098123118405812672/682119494312515965977783203125:ℝ),(4520487285688798777343165627524331114368/2046358482937547897933349609375:ℝ),(4371478048713404895050109888421573476352/2046358482937547897933349609375:ℝ),(50052483566870519145722110511611904/72759412726668369704296875:ℝ)],
![(965372912862174045783966918798889101136/682119494312515965977783203125:ℝ),(8396425433394660613406918173737647574944/2046358482937547897933349609375:ℝ),(8105829819204818233518178063078401560576/2046358482937547897933349609375:ℝ),(8271530193140299797213540327598063616/6496376136309675866455078125:ℝ)],
![(446462605157830143579868795680483288464/682119494312515965977783203125:ℝ),(3875938147705861836063752546213316460576/2046358482937547897933349609375:ℝ),(3734351770491413338468068174656828084224/2046358482937547897933349609375:ℝ),(8872636374229341371472821074476335104/15158210984722577021728515625:ℝ)]]
theorem admission006_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1218471181763672978870474085545151/127156289932131687385088000000000000:ℝ) admission006_09_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission006_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_09_coefficients]
def admission006_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2571117343496731801475887808/12366832357177734375:ℝ),(52001181068787853888966551616/86567826500244140625:ℝ),(50015864811927123818564459264/86567826500244140625:ℝ),(1779172033155293615547680256/9618647388916015625:ℝ)],
![(531151311406134651589925536/1374092484130859375:ℝ),(10719305063573350281905998304/9618647388916015625:ℝ),(10285921219135817751111060352/9618647388916015625:ℝ),(131387402025591401213381632/384745895556640625:ℝ)],
![(440740728523260843028513052/2473366471435546875:ℝ),(6336783246828144698776567676/12366832357177734375:ℝ),(6063373070930125932836377072/12366832357177734375:ℝ),(214477754933759147133597184/1374092484130859375:ℝ)]]
theorem admission006_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3770116785944985008207763/1475420570255360000000000000:ℝ) admission006_10_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission006_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_10_coefficients]
def admission006_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13846365755590535894932147733307392/1047735543264024523741875:ℝ),(1522352013236624919312901365817344/38805020120889797175625:ℝ),(40669929631679979121534722827616256/1047735543264024523741875:ℝ),(894186068658776146334568912257024/69849036217601634916125:ℝ)],
![(27277408950063663453068509286397952/1047735543264024523741875:ℝ),(8996435793084620052179339044763648/116415060362669391526875:ℝ),(80107620983205275710061891891757056/1047735543264024523741875:ℝ),(8805702598502452897838783258427392/349245181088008174580625:ℝ)],
![(2686208638894625511627272310618112/209547108652804904748375:ℝ),(4429379753374745294240634947311616/116415060362669391526875:ℝ),(1577507654061011863541086762565632/41909421730560980949675:ℝ),(4334772255208572166165938697142272/349245181088008174580625:ℝ)]]
theorem admission006_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1033490241815703431645855593/5086251597285267495403520000:ℝ) admission006_11_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission006_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_11_coefficients]
def admission006_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5520908634151714816/10986328125:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/10986328125:ℝ)],
![(11041817268303429632/10986328125:ℝ),(11041817268303429632/3662109375:ℝ),(11041817268303429632/3662109375:ℝ),(11041817268303429632/10986328125:ℝ)],
![(5520908634151714816/10986328125:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/10986328125:ℝ)]]
theorem admission006_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission006_12_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission006_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_12_coefficients]
def admission006_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(194287637771172446208/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(194287637771172446208/762939453125:ℝ)],
![(388575275542344892416/762939453125:ℝ),(1165725826627034677248/762939453125:ℝ),(1165725826627034677248/762939453125:ℝ),(388575275542344892416/762939453125:ℝ)],
![(194287637771172446208/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(194287637771172446208/762939453125:ℝ)]]
theorem admission006_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission006_13_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission006_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_13_coefficients]
def admission006_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(549755813888/9:ℝ),(549755813888/3:ℝ),(549755813888/3:ℝ),(549755813888/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)]]
theorem admission006_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission006_14_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission006_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission006_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission006_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission006_14_coefficients]
theorem admission006_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission006_00_pos hd hp
 · exact admission006_01_pos hd hp
 · exact admission006_02_pos hd hp
 · exact admission006_03_pos hd hp
 · exact admission006_04_pos hd hp
 · exact admission006_05_pos hd hp
 · exact admission006_06_pos hd hp
 · exact admission006_07_pos hd hp
 · exact admission006_08_pos hd hp
 · exact admission006_09_pos hd hp
 · exact admission006_10_pos hd hp
 · exact admission006_11_pos hd hp
 · exact admission006_12_pos hd hp
 · exact admission006_13_pos hd hp
 · exact admission006_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission006_all
