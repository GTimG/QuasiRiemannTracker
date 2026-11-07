/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission020_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43687626296988270592/23638787823:ℝ),(388389119183376351232/70916363469:ℝ),(383589601693858267136/70916363469:ℝ),(126263361401446727680/70916363469:ℝ)],
![(87375252593976541184/23638787823:ℝ),(776778238366752702464/70916363469:ℝ),(767179203387716534272/70916363469:ℝ),(252526722802893455360/70916363469:ℝ)],
![(43687626296988270592/23638787823:ℝ),(388389119183376351232/70916363469:ℝ),(383589601693858267136/70916363469:ℝ),(126263361401446727680/70916363469:ℝ)]]
theorem admission020_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission020_00_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission020_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_00_coefficients]
def admission020_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(95105109089157382144/70916363469:ℝ),(282630972707472146432/70916363469:ℝ),(279946618147472146432/70916363469:ℝ),(30806918176385794048/23638787823:ℝ)],
![(190210218178314764288/70916363469:ℝ),(565261945414944292864/70916363469:ℝ),(559893236294944292864/70916363469:ℝ),(61613836352771588096/23638787823:ℝ)],
![(95105109089157382144/70916363469:ℝ),(282630972707472146432/70916363469:ℝ),(279946618147472146432/70916363469:ℝ),(30806918176385794048/23638787823:ℝ)]]
theorem admission020_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission020_01_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission020_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_01_coefficients]
def admission020_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6038205704005671190528/8864545433625:ℝ),(89765603555396179460096/44322727168125:ℝ),(88958121550707291062272/44322727168125:ℝ),(29383546515339467554816/44322727168125:ℝ)],
![(12076411408011342381056/8864545433625:ℝ),(179531207110792358920192/44322727168125:ℝ),(177916243101414582124544/44322727168125:ℝ),(58767093030678935109632/44322727168125:ℝ)],
![(6038205704005671190528/8864545433625:ℝ),(89765603555396179460096/44322727168125:ℝ),(88958121550707291062272/44322727168125:ℝ),(29383546515339467554816/44322727168125:ℝ)]]
theorem admission020_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission020_02_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission020_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_02_coefficients]
def admission020_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(72385202559379308544/70916363469:ℝ),(640150490240983760896/212749090407:ℝ),(628893139847553744896/212749090407:ℝ),(205898257284707909632/212749090407:ℝ)],
![(20412569229804437504/10130909067:ℝ),(180482322487725522944/30392727201:ℝ),(1240880092710477758464/212749090407:ℝ),(406167789122292285440/212749090407:ℝ)],
![(70502782049251753984/70916363469:ℝ),(623225767173094899712/212749090407:ℝ),(611986952862924013568/212749090407:ℝ),(200269531837584375808/212749090407:ℝ)]]
theorem admission020_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (11936994304513/24206118730752:ℝ) admission020_03_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission020_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_03_coefficients]
def admission020_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71546281227418750976/422121211125:ℝ),(97358104877562646528/196989898525:ℝ),(1418665518873687621632/2954848477875:ℝ),(459117914302179180544/2954848477875:ℝ)],
![(5128232421281076372992/14774242389375:ℝ),(4986143798714381378048/4924747463125:ℝ),(4845385865486468120576/4924747463125:ℝ),(4705958621597336600576/14774242389375:ℝ)],
![(2624112578321420088832/14774242389375:ℝ),(2552191176775315214848/4924747463125:ℝ),(1063261428870138036224/2110606055625:ℝ),(114779478575544795136/703535351875:ℝ)]]
theorem admission020_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656773444607991/8068706243584000:ℝ) admission020_04_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission020_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_04_coefficients]
def admission020_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3993528421068237299968/44322727168125:ℝ),(12022933676332072780544/44322727168125:ℝ),(1723205526545771959552/6331818166875:ℝ),(192049210978884201728/2110606055625:ℝ)],
![(1466613616525127151616/8864545433625:ℝ),(22100576964415940260864/44322727168125:ℝ),(4439238357717187522048/8864545433625:ℝ),(825409211866181456384/4924747463125:ℝ)],
![(3339539661557398458112/44322727168125:ℝ),(287932665373824785152/1266363633375:ℝ),(10133753102765533893376/44322727168125:ℝ),(1131883158746354957056/14774242389375:ℝ)]]
theorem admission020_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (13045076802958587727/330494207737200640000:ℝ) admission020_05_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission020_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_05_coefficients]
def admission020_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(94814055758393353046092190216192/369202048578751498842375:ℝ),(815025943387206458170367175774208/1107606145736254496527125:ℝ),(777475774217324445469266206523392/1107606145736254496527125:ℝ),(49377575729278648007435120279552/221521229147250899305425:ℝ)],
![(6777181098320451927709552392856064/12922071700256302459483125:ℝ),(58292249598558229516047817989531136/38766215100768907378449375:ℝ),(55642841548294604834943361418461184/38766215100768907378449375:ℝ),(3536368655609570589684840121499648/7753243020153781475689875:ℝ)],
![(3458689146776684571096325735289344/12922071700256302459483125:ℝ),(29766341580006003480084966837433856/38766215100768907378449375:ℝ),(28431189450688249243519044190142464/38766215100768907378449375:ℝ),(1808153505084817909424610911715328/7753243020153781475689875:ℝ)]]
theorem admission020_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (23545062889708827975957451/201633545463808818567782400:ℝ) admission020_06_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission020_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_06_coefficients]
def admission020_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(103753926567124442287264882528256/209547108652804904748375:ℝ),(304975336566118614870199971647488/209547108652804904748375:ℝ),(99579413396846278489443749593088/69849036217601634916125:ℝ),(97516830191544662885396159660032/209547108652804904748375:ℝ)],
![(20534047186671078052150639325696/21382358025796418851875:ℝ),(2956650826306267289605989222994432/1047735543264024523741875:ℝ),(965094084346467320044676965400576/349245181088008174580625:ℝ),(5398855650742957114762417143808/5987060247222997278525:ℝ)],
![(487398679311260613119056914317824/1047735543264024523741875:ℝ),(1431774143475674215254989364756992/1047735543264024523741875:ℝ),(467197017362235927597458217435136/349245181088008174580625:ℝ),(91443117584458836131288440373248/209547108652804904748375:ℝ)]]
theorem admission020_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (348827810609660477185395967/1525875479185580248621056000:ℝ) admission020_07_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission020_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_07_coefficients]
def admission020_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(537204177830534185022545192839575439983/85264936789064495747222900390625:ℝ),(5271866165877468927022017284990754679379/255794810367193487241668701171875:ℝ),(90618565528273360052811043642531479847/4060235085193547416534423828125:ℝ),(2048541652603414118879247892797767370931/255794810367193487241668701171875:ℝ)],
![(6440692324761777830431686553447580335531/341059747156257982988891601562500:ℝ),(43571956488961405975070903800120619927507/730842315334838534976196289062500:ℝ),(2964960942916714310838206463016406709758/47369409327258053192901611328125:ℝ),(5590770519018917645275994531157447322214/255794810367193487241668701171875:ℝ)],
![(4291875613439641090341505782089278575599/341059747156257982988891601562500:ℝ),(199566372105180463285055980901029245904969/5115896207343869744833374023437500:ℝ),(5723233035260575330666232861560618334629/142108227981774159578704833984375:ℝ),(506032695202214789485249519765668564469/36542115766741926748809814453125:ℝ)]]
theorem admission020_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (537204177830534185022545192839575439983/162760051113128559852912640000000000000000:ℝ) admission020_08_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission020_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_08_coefficients]
def admission020_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8327537565160265565004130345732833408/409271696587509579586669921875:ℝ),(7824601330402967147341392377513476544/136423898862503193195556640625:ℝ),(4395264089678733085129189371826413568/81854339317501915917333984375:ℝ),(758920705293281216830922978133274624/45474632954167731065185546875:ℝ)],
![(13844066682429365014966617595080751952/409271696587509579586669921875:ℝ),(64507429794954706134595256911813604408/682119494312515965977783203125:ℝ),(179482455293176259525817413074123672064/2046358482937547897933349609375:ℝ),(81752372761578952445548664391401472/3031642196944515404345703125:ℝ)],
![(788075588181299921423212464192559792/58467385226787082798095703125:ℝ),(25384423142939870397888295024246221688/682119494312515965977783203125:ℝ),(69600853051207932397587678778463332864/2046358482937547897933349609375:ℝ),(467364886130403069852306987737747456/45474632954167731065185546875:ℝ)]]
theorem admission020_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (342308266208791310926982657034483/63578144966065843692544000000000000:ℝ) admission020_09_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission020_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_09_coefficients]
def admission020_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(492261756327948744102796864/86567826500244140625:ℝ),(1370644115537851842116710592/86567826500244140625:ℝ),(1265071327386222083175030592/86567826500244140625:ℝ),(42966769033479887240124096/9618647388916015625:ℝ)],
![(89079582904315229427676512/9618647388916015625:ℝ),(244792449478116749299709856/9618647388916015625:ℝ),(222455627030997464378890176/9618647388916015625:ℝ),(66745483113445944506856832/9618647388916015625:ℝ)],
![(304445820423911220348913334/86567826500244140625:ℝ),(817784900169634555120749754/86567826500244140625:ℝ),(722645123646765167214290756/86567826500244140625:ℝ),(23257622461443884160272704/9618647388916015625:ℝ)]]
theorem admission020_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3270603158640546210038349/2581985997946880000000000000:ℝ) admission020_10_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission020_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_10_coefficients]
def admission020_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141835589599736923750997712769024/349245181088008174580625:ℝ),(1250780157923284797061429083713536/1047735543264024523741875:ℝ),(1225275877670878827378356485881856/1047735543264024523741875:ℝ),(133334162848934933856640180158464/349245181088008174580625:ℝ)],
![(5609685427145705488675846281728/7127452675265472950625:ℝ),(2423259317083212865956456471899648/1047735543264024523741875:ℝ),(2373110894870408406228403299909632/1047735543264024523741875:ℝ),(295038223077186379850398564352/399137349814866485235:ℝ)],
![(133038996330402645194118755035648/349245181088008174580625:ℝ),(1172479159159928068895027388186112/1047735543264024523741875:ℝ),(1147835017199529578850046814027776/1047735543264024523741875:ℝ),(124824282343603148512458563649536/349245181088008174580625:ℝ)]]
theorem admission020_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (476166848539745897340616469/2543125798642633747701760000:ℝ) admission020_11_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission020_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_11_coefficients]
def admission020_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)],
![(345056789634482176/10986328125:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/10986328125:ℝ)],
![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)]]
theorem admission020_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission020_12_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission020_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_12_coefficients]
def admission020_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)],
![(12142977360698277888/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(12142977360698277888/762939453125:ℝ)],
![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)]]
theorem admission020_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission020_13_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission020_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_13_coefficients]
def admission020_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission020_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission020_14_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission020_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_14_coefficients]
theorem admission020_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission020_00_pos hd hp
 · exact admission020_01_pos hd hp
 · exact admission020_02_pos hd hp
 · exact admission020_03_pos hd hp
 · exact admission020_04_pos hd hp
 · exact admission020_05_pos hd hp
 · exact admission020_06_pos hd hp
 · exact admission020_07_pos hd hp
 · exact admission020_08_pos hd hp
 · exact admission020_09_pos hd hp
 · exact admission020_10_pos hd hp
 · exact admission020_11_pos hd hp
 · exact admission020_12_pos hd hp
 · exact admission020_13_pos hd hp
 · exact admission020_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission020_all
