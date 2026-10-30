/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission015_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16468879378714338525184/70916363469:ℝ),(49099469016813858193408/70916363469:ℝ),(48792299897484700811264/70916363469:ℝ),(16161710259385181143040/70916363469:ℝ)],
![(32937758757428677050368/70916363469:ℝ),(98198938033627716386816/70916363469:ℝ),(97584599794969401622528/70916363469:ℝ),(32323420518770362286080/70916363469:ℝ)],
![(16468879378714338525184/70916363469:ℝ),(49099469016813858193408/70916363469:ℝ),(48792299897484700811264/70916363469:ℝ),(16161710259385181143040/70916363469:ℝ)]]
theorem admission015_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission015_00_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission015_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_00_coefficients]
def admission015_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12001655271572144914432/70916363469:ℝ),(35833167122876434743296/70916363469:ℝ),(35661368431036434743296/70916363469:ℝ),(3943285526577381638144/23638787823:ℝ)],
![(24003310543144289828864/70916363469:ℝ),(71666334245752869486592/70916363469:ℝ),(71322736862072869486592/70916363469:ℝ),(7886571053154763276288/23638787823:ℝ)],
![(12001655271572144914432/70916363469:ℝ),(35833167122876434743296/70916363469:ℝ),(35661368431036434743296/70916363469:ℝ),(3943285526577381638144/23638787823:ℝ)]]
theorem admission015_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission015_01_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission015_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_01_coefficients]
def admission015_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1270924267421180234825728/14774242389375:ℝ),(11386639558490533255970816/44322727168125:ℝ),(2266992142038088879702016/8864545433625:ℝ),(3761093953963451847016448/44322727168125:ℝ)],
![(2541848534842360469651456/14774242389375:ℝ),(22773279116981066511941632/44322727168125:ℝ),(4533984284076177759404032/8864545433625:ℝ),(7522187907926903694032896/44322727168125:ℝ)],
![(1270924267421180234825728/14774242389375:ℝ),(11386639558490533255970816/44322727168125:ℝ),(2266992142038088879702016/8864545433625:ℝ),(3761093953963451847016448/44322727168125:ℝ)]]
theorem admission015_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission015_02_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission015_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_02_coefficients]
def admission015_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3854873865898921295872/30392727201:ℝ),(80231287604033534033920/212749090407:ℝ),(79512087868029720854528/212749090407:ℝ),(26264917325288635891712/212749090407:ℝ)],
![(7683972362066399854592/30392727201:ℝ),(159921589021038916665344/212749090407:ℝ),(158483497922843436384256/212749090407:ℝ),(52349715436269318701056/212749090407:ℝ)],
![(3829098496167478558720/30392727201:ℝ),(79690301417005382631424/212749090407:ℝ),(78971410054813715529728/212749090407:ℝ),(3726399730140097544192/30392727201:ℝ)]]
theorem admission015_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (6940960381441/13832067846144:ℝ) admission015_03_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission015_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_03_coefficients]
def admission015_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(303279339019567782797312/14774242389375:ℝ),(896658903903141692284928/14774242389375:ℝ),(883542086722551151591424/14774242389375:ℝ),(290162521838977242103808/14774242389375:ℝ)],
![(203438213061269967065088/4924747463125:ℝ),(72180091165269075488768/590969695575:ℝ),(1778185626940288903675904/14774242389375:ℝ),(194665995664123972550656/4924747463125:ℝ)],
![(307035300164242118397952/14774242389375:ℝ),(302614458409528398311424/4924747463125:ℝ),(59642902681182516805632/984949492625:ℝ),(58767093030678935109632/2954848477875:ℝ)]]
theorem admission015_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (51885102124031289/645496499486720000:ℝ) admission015_04_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission015_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_04_coefficients]
def admission015_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23886576388603821979648/2110606055625:ℝ),(1506851279323107229386752/44322727168125:ℝ),(1508758394609180327815168/44322727168125:ℝ),(503525219446753360001024/44322727168125:ℝ)],
![(15596425612394204028928/703535351875:ℝ),(2951984051307730818433024/44322727168125:ℝ),(2956063390082242576928768/44322727168125:ℝ),(986654152355346612318208/44322727168125:ℝ)],
![(22902700448578790107136/2110606055625:ℝ),(1445132771984623589046272/44322727168125:ℝ),(57892199818922489964544/1772909086725:ℝ),(483128932908593252317184/44322727168125:ℝ)]]
theorem admission015_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (33548877610222837071/755415331970744320000:ℝ) admission015_05_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission015_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_05_coefficients]
def admission015_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1175893890119950799158844595621699584/38766215100768907378449375:ℝ),(3444231135904893896553344054895681536/38766215100768907378449375:ℝ),(3361607083451948734033945081226985472/38766215100768907378449375:ℝ),(218653511921246255740049124390600704/7753243020153781475689875:ℝ)],
![(2364908797332040593859641384803332096/38766215100768907378449375:ℝ),(6927490940497936138592906470894956544/38766215100768907378449375:ℝ),(6761911969647623421500857402306592768/38766215100768907378449375:ℝ),(439865051188414598813358463242993664/7753243020153781475689875:ℝ)],
![(1189014907212089794700796789181632512/38766215100768907378449375:ℝ),(3483259804593042242039562415999275008/38766215100768907378449375:ℝ),(3400304886195674687466912321079607296/38766215100768907378449375:ℝ),(6320329693347666944951695395782656/221521229147250899305425:ℝ)]]
theorem admission015_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (13032764906957522376778669619/112914785459732938397958144000:ℝ) admission015_06_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission015_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_06_coefficients]
def admission015_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(63944799276637361625117078733119488/1047735543264024523741875:ℝ),(189806450494080716601257920021061632/1047735543264024523741875:ℝ),(6955056501165373077128361701015552/38805020120889797175625:ℝ),(12384974862804343621264984927895552/209547108652804904748375:ℝ)],
![(126901829734151939307301764746924032/1047735543264024523741875:ℝ),(376665632778616000806466324314411008/1047735543264024523741875:ℝ),(1971649511404093996990249596616704/5543574302984256739375:ℝ),(24575590922181940786398522838614016/209547108652804904748375:ℝ)],
![(62957030457514577682184686013804544/1047735543264024523741875:ℝ),(186859182284535284205208404293349376/1047735543264024523741875:ℝ),(6846490078663284901803385475301376/38805020120889797175625:ℝ),(12190616059377597165133537910718464/209547108652804904748375:ℝ)]]
theorem admission015_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1453234679624747892038051833/6103501916742320994484224000:ℝ) admission015_07_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission015_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_07_coefficients]
def admission015_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5805101609714757772838811510594911801426/8700503753986173035430908203125:ℝ),(388294002166316778467996406372289394038118/182710578833709633744049072265625:ℝ),(958630228569694693062917969806810312532714/426324683945322478736114501953125:ℝ),(1011168834052872668313100531005291901640938/1278974051835967436208343505859375:ℝ)],
![(13297316643234901371433935628672882457266/8700503753986173035430908203125:ℝ),(881577797196596129984721525884039958938338/182710578833709633744049072265625:ℝ),(431846285969872981942098492658806085082564/85264936789064495747222900390625:ℝ),(2261327622315679641829000861300489816138196/1278974051835967436208343505859375:ℝ)],
![(1498443006704028719719024823615594131168/1740100750797234607086181640625:ℝ),(98656759006055870303345023902350112980044/36542115766741926748809814453125:ℝ),(1200601201279670216647574493487220112880106/426324683945322478736114501953125:ℝ),(178594112608972424787985761470742559213894/182710578833709633744049072265625:ℝ)]]
theorem admission015_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (2902550804857378886419405755297455900713/1062922782779615084753715200000000000000000:ℝ) admission015_08_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission015_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_08_coefficients]
def admission015_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31757873127646209830611831667207868608/13920806006377876856689453125:ℝ),(1928023190559862257341251175805263146624/292336926133935413990478515625:ℝ),(12989199703148804888584991684781042614272/2046358482937547897933349609375:ℝ),(30825652390311315134233428451576905728/15158210984722577021728515625:ℝ)],
![(60558697171761245839826547928786246432/13920806006377876856689453125:ℝ),(3671889484553171102888384328378807820736/292336926133935413990478515625:ℝ),(24704146849853626664005899942032594444288/2046358482937547897933349609375:ℝ),(175624128128655790102084859016804564992/45474632954167731065185546875:ℝ)],
![(28800824044115036009214716261578377824/13920806006377876856689453125:ℝ),(249123756284758406506733307510506382016/41762418019133630570068359375:ℝ),(11714947146704821775420908257251551830016/2046358482937547897933349609375:ℝ),(1696881039953507034681317829838241792/928053733758525123779296875:ℝ)]]
theorem admission015_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (38838524779209297973968151012533/5190052650291089281024000000000000:ℝ) admission015_09_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission015_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_09_coefficients]
def admission015_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(53356501692059050243960608464/86567826500244140625:ℝ),(152994853951030523823570663184/86567826500244140625:ℝ),(20848762844780734333130821568/12366832357177734375:ℝ),(5144797128125164361367299584/9618647388916015625:ℝ)],
![(101181354413839804940893328336/86567826500244140625:ℝ),(57910298692865301616913115344/17313565300048828125:ℝ),(275600026558254251970607418432/86567826500244140625:ℝ),(1384607347075799386141828096/1374092484130859375:ℝ)],
![(3185737800399034917539772172/5771188433349609375:ℝ),(45480519245906899501414484716/28855942166748046875:ℝ),(43181623993668252409037074352/28855942166748046875:ℝ),(4543285568457253956773816832/9618647388916015625:ℝ)]]
theorem admission015_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (79862441633037667208914749/41311775967150080000000000000:ℝ) admission015_10_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission015_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_10_coefficients]
def admission015_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(52443963610232872020782744732770304/1047735543264024523741875:ℝ),(5765633054414829431637505302945792/38805020120889797175625:ℝ),(154019973128702611537859010035187712/1047735543264024523741875:ℝ),(16930614756578362968143037196140544/349245181088008174580625:ℝ)],
![(104057282098230927367973917105106944/1047735543264024523741875:ℝ),(6863689150763743532485778703478784/23283012072533878305375:ℝ),(43653638528156551144243273220489216/149676506180574931963125:ℝ),(33588913336986108805272262663995392/349245181088008174580625:ℝ)],
![(10322663697599611069438234474467328/209547108652804904748375:ℝ),(17021546590574229367516377608556544/116415060362669391526875:ℝ),(6062219862735729858873756100329472/41909421730560980949675:ℝ),(16658298580407745837129225467854848/349245181088008174580625:ℝ)]]
theorem admission015_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1985823938895195226327088531/10172503194570534990807040000:ℝ) admission015_11_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission015_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_11_coefficients]
def admission015_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22083634536606859264/10986328125:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/10986328125:ℝ)],
![(44167269073213718528/10986328125:ℝ),(44167269073213718528/3662109375:ℝ),(44167269073213718528/3662109375:ℝ),(44167269073213718528/10986328125:ℝ)],
![(22083634536606859264/10986328125:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/10986328125:ℝ)]]
theorem admission015_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission015_12_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission015_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_12_coefficients]
def admission015_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(777150551084689784832/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(777150551084689784832/762939453125:ℝ)],
![(1554301102169379569664/762939453125:ℝ),(4662903306508138708992/762939453125:ℝ),(4662903306508138708992/762939453125:ℝ),(1554301102169379569664/762939453125:ℝ)],
![(777150551084689784832/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(777150551084689784832/762939453125:ℝ)]]
theorem admission015_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission015_13_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission015_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_13_coefficients]
def admission015_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)],
![(2199023255552/9:ℝ),(2199023255552/3:ℝ),(2199023255552/3:ℝ),(2199023255552/9:ℝ)],
![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)]]
theorem admission015_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission015_14_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission015_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_14_coefficients]
theorem admission015_all {δ p : ℝ}
 (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission015_00_pos hd hp
 · exact admission015_01_pos hd hp
 · exact admission015_02_pos hd hp
 · exact admission015_03_pos hd hp
 · exact admission015_04_pos hd hp
 · exact admission015_05_pos hd hp
 · exact admission015_06_pos hd hp
 · exact admission015_07_pos hd hp
 · exact admission015_08_pos hd hp
 · exact admission015_09_pos hd hp
 · exact admission015_10_pos hd hp
 · exact admission015_11_pos hd hp
 · exact admission015_12_pos hd hp
 · exact admission015_13_pos hd hp
 · exact admission015_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission015_all
