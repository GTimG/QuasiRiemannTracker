/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission034_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6611840371125148587941823512576/3376969689:ℝ),(416525329610230300846341983567872/70916363469:ℝ),(416504715839576240652349085843456/70916363469:ℝ),(138828034022974060152785396039680/70916363469:ℝ)],
![(13223680742250297175883647025152/3376969689:ℝ),(833050659220460601692683967135744/70916363469:ℝ),(833009431679152481304698171686912/70916363469:ℝ),(277656068045948120305570792079360/70916363469:ℝ)],
![(6611840371125148587941823512576/3376969689:ℝ),(416525329610230300846341983567872/70916363469:ℝ),(416504715839576240652349085843456/70916363469:ℝ),(138828034022974060152785396039680/70916363469:ℝ)]]
theorem admission034_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission034_00_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission034_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_00_coefficients]
def admission034_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14518460495383718023513759547392/10130909067:ℝ),(304876141188012010024028950495232/70916363469:ℝ),(304864611972965941554268950495232/70916363469:ℝ),(33872564750879985898278772277248/23638787823:ℝ)],
![(29036920990767436047027519094784/10130909067:ℝ),(609752282376024020048057900990464/70916363469:ℝ),(609729223945931883108537900990464/70916363469:ℝ),(67745129501759971796557544554496/23638787823:ℝ)],
![(14518460495383718023513759547392/10130909067:ℝ),(304876141188012010024028950495232/70916363469:ℝ),(304864611972965941554268950495232/70916363469:ℝ),(33872564750879985898278772277248/23638787823:ℝ)]]
theorem admission034_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission034_01_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission034_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_01_coefficients]
def admission034_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(923171976220427366249603616735232/1266363633375:ℝ),(96929589394342626161885131839635456/44322727168125:ℝ),(96926121285540378867561883922071552/44322727168125:ℝ),(32307551058912710524412878668169216/44322727168125:ℝ)],
![(1846343952440854732499207233470464/1266363633375:ℝ),(193859178788685252323770263679270912/44322727168125:ℝ),(193852242571080757735123767844143104/44322727168125:ℝ),(64615102117825421048825757336338432/44322727168125:ℝ)],
![(923171976220427366249603616735232/1266363633375:ℝ),(96929589394342626161885131839635456/44322727168125:ℝ),(96926121285540378867561883922071552/44322727168125:ℝ),(32307551058912710524412878668169216/44322727168125:ℝ)]]
theorem admission034_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission034_02_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission034_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_02_coefficients]
def admission034_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(75373808334448692793547883020288/70916363469:ℝ),(678316099570336093132111539601408/212749090407:ℝ),(678267925098064597128052132020224/212749090407:ℝ),(226073250531074582376584241479680/212749090407:ℝ)],
![(150739558159784116904345234046976/70916363469:ℝ),(1356559672894182378848513857421312/212749090407:ℝ),(1356463324285265634333600608419840/212749090407:ℝ),(452122325870435606198122453139456/212749090407:ℝ)],
![(75365749825335424110797351026688/70916363469:ℝ),(678243573323846285716402317819904/212749090407:ℝ),(678195399187201037205548476399616/212749090407:ℝ),(226049075339361023821538211659776/212749090407:ℝ)]]
theorem admission034_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (784265275428079/1549191598768128:ℝ) admission034_03_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission034_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_03_coefficients]
def admission034_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(822816415778357921906315008933888/4924747463125:ℝ),(493632023572790824981296612114432/984949492625:ℝ),(2467870999171104282681303428497408/4924747463125:ℝ),(822527297085508079681135376859136/4924747463125:ℝ)],
![(329159437027812330005190821281792/984949492625:ℝ),(705259038227681121726694260998144/703535351875:ℝ),(14808705003983900981830021562761216/14774242389375:ℝ),(4935656756619782375647304401027072/14774242389375:ℝ)],
![(822980769360703728119639097475072/4924747463125:ℝ),(2468653149729813727180376766414848/4924747463125:ℝ),(7405092006470588133786111277268992/14774242389375:ℝ),(2468074865363258136603898270449664/14774242389375:ℝ)]]
theorem admission034_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (6574958953970597901/82623551934300160000:ℝ) admission034_04_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission034_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_04_coefficients]
def admission034_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(124796729699294791463157930917888/1266363633375:ℝ),(13103750649836537102557517535248384/44322727168125:ℝ),(2620768926921910184374558263345152/8864545433625:ℝ),(1455993174749443840175267121201152/14774242389375:ℝ)],
![(8733033258317394494114039651631104/44322727168125:ℝ),(26199288115172462186069630358913024/44322727168125:ℝ),(26199476362112941898053633087373312/44322727168125:ℝ),(970357945028652689566449153343488/4924747463125:ℝ)],
![(4365147718842076792903512069505024/44322727168125:ℝ),(2619107493067185016702422564732928/8864545433625:ℝ),(13095631727503390976180841770647552/44322727168125:ℝ),(1455080660336514228524080338829312/14774242389375:ℝ)]]
theorem admission034_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (65045769793422174347989441/1386193177488971593154560000:ℝ) admission034_05_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission034_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_05_coefficients]
def admission034_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(344809662853047014901636370003785177309904896/1435785744472922495498125:ℝ),(27924126709582177917845366634338967552121634816/38766215100768907378449375:ℝ),(27918671154952922225165164473608766198900588544/38766215100768907378449375:ℝ),(1860881068478755194274094410080479686829277184/7753243020153781475689875:ℝ)],
![(2069048755609069670977616409602764992302546944/4307357233418767486494375:ℝ),(55853404095062734114516633463560268832946782208/38766215100768907378449375:ℝ),(55842492642479793080939278936602253267558203392/38766215100768907378449375:ℝ),(3722105469576041921175076584978813873066868736/7753243020153781475689875:ℝ)],
![(1034619767049928626272707299591409460372832256/4307357233418767486494375:ℝ),(27929277385480556196671266829221301280825147392/38766215100768907378449375:ℝ),(27923821487526870855774114462993487068657614848/38766215100768907378449375:ℝ),(1861224401097286726900982174898334186237591552/7753243020153781475689875:ℝ)]]
theorem admission034_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1652794406651341313962161914191/14453092538845816114938642432000:ℝ) admission034_06_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission034_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_06_coefficients]
def admission034_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(534545533558144637239215216491136987739193344/1047735543264024523741875:ℝ),(1603499890549238087336332159372160382651072512/1047735543264024523741875:ℝ),(534454394894190282285480507797755226075693056/349245181088008174580625:ℝ),(855054124306363834814919328819587653304320/1676376869222439237987:ℝ)],
![(152708659778062807401487293424717776149282816/149676506180574931963125:ℝ),(3206608451774232994988800263996591547221016576/1047735543264024523741875:ℝ),(1068778352241894818026056099536020750727118848/349245181088008174580625:ℝ),(213737444679578222179955817716899027601063936/209547108652804904748375:ℝ)],
![(534415084888295014571195837481887445305786368/1047735543264024523741875:ℝ),(1603108561224994907652468104624431164569944064/1047735543264024523741875:ℝ),(534323957347704535740575591738265524651425792/349245181088008174580625:ℝ),(106855679141282742828090901614450570938023936/209547108652804904748375:ℝ)]]
theorem admission034_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (23726727058922035335639866641/97656030667877135911747584000:ℝ) admission034_07_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission034_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_07_coefficients]
def admission034_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141831377925123174949125927806700181040866182939136/28421645596354831915740966796875:ℝ),(19158760910410504184932298968128706386466010295333376/1278974051835967436208343505859375:ℝ),(710010578790880966710646685301599508689861434357248/47369409327258053192901611328125:ℝ),(1278787344703594713341176677729824068605083332914688/255794810367193487241668701171875:ℝ)],
![(284375779555508507849786894393822212845583209746432/28421645596354831915740966796875:ℝ),(38413770642368926831307307221205603027955243401356288/1278974051835967436208343505859375:ℝ),(4270756744243064505828608225841657617232030705861632/142108227981774159578704833984375:ℝ),(2563990027140965710177069029119557576885989477997568/255794810367193487241668701171875:ℝ)],
![(20363485947197904700094423798160290257816718115328/4060235085193547416534423828125:ℝ),(2750715675994060378053572607582413805927033300860416/182710578833709633744049072265625:ℝ),(2140725007870421605696668169936859091162446402789888/142108227981774159578704833984375:ℝ),(257040536487474199367178470277946701656181229016576/51158962073438697448333740234375:ℝ)]]
theorem admission034_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (831043230030018603217534733242383873286325290659/349524548313087780405919179572510720000000000000000:ℝ) admission034_08_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission034_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_08_coefficients]
def admission034_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7370556929230987286242476947855691819862436583424/409271696587509579586669921875:ℝ),(12280323787394986946650690984080012650745307856896/227373164770838655325927734375:ℝ),(110487475457338287407598808063854891329408827654144/2046358482937547897933349609375:ℝ),(163632648964501187518662610457721944983472177152/9094926590833546213037109375:ℝ)],
![(2104262966356876075182292050740414767631640479744/58467385226787082798095703125:ℝ),(8180620267130958628442790347790992111578663878656/75791054923612885108642578125:ℝ),(220805885402050058211842860802323351506049210253312/2046358482937547897933349609375:ℝ),(1635074266936748823448119867687128010543482273792/45474632954167731065185546875:ℝ)],
![(7359283835267145240033567407327211553559046774784/409271696587509579586669921875:ℝ),(12261537013997888938677680059292963683990683779072/227373164770838655325927734375:ℝ),(110318409944711770804244052738468460176640382599168/2046358482937547897933349609375:ℝ),(272303674038080961951602271799506095208707129344/15158210984722577021728515625:ℝ)]]
theorem admission034_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (34827011551538030539126402319930589/4069001277828213996322816000000000000:ℝ) admission034_09_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission034_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_09_coefficients]
def admission034_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137122891467959263573564663377107402752/28855942166748046875:ℝ),(82241197339101480031771321672618597888/5771188433349609375:ℝ),(58720471870806427879252708311551967232/4122277452392578125:ℝ),(45653402622782143386619290856626061312/9618647388916015625:ℝ)],
![(822031518898823737656469702536129544192/86567826500244140625:ℝ),(2465118588195501583974686238431943348224/86567826500244140625:ℝ),(2464142644336255106056549315607498063872/86567826500244140625:ℝ),(18245679445357218641311908993592983552/1923729477783203125:ℝ)],
![(410662765792119740266141854228327694336/86567826500244140625:ℝ),(1231500392021128266962642024548135018496/86567826500244140625:ℝ),(1231012498982095453094040239083286953984/86567826500244140625:ℝ),(6510712265933901440548751091483803648/1374092484130859375:ℝ)]]
theorem admission034_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3410759986925702132572114923/1510830663941488640000000000000:ℝ) admission034_10_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission034_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_10_coefficients]
def admission034_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(146164584940987519912323579385489247449382912/349245181088008174580625:ℝ),(1315369456182094656859654755961388806363414528/1047735543264024523741875:ℝ),(1315257651975612790364940497817176896178225152/1047735543264024523741875:ℝ),(29225463374432046216150432000817055477530624/69849036217601634916125:ℝ)],
![(41756087922708798128756975933605796751867904/49892168726858310654375:ℝ),(2630409936851256342695644684925253313145864192/1047735543264024523741875:ℝ),(2630186342731943164561213493903672467326500864/1047735543264024523741875:ℝ),(292218084085857194189821767861380295323287552/349245181088008174580625:ℝ)],
![(146128030517974066988975252149751329813692416/349245181088008174580625:ℝ),(1315040480669161685835989928963864506782449664/1047735543264024523741875:ℝ),(1314928690756330374196272996086495571148275712/1047735543264024523741875:ℝ),(146090767213696963109069607857295017935634432/349245181088008174580625:ℝ)]]
theorem admission034_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (32438666689160059044343322267/162760051113128559852912640000:ℝ) admission034_11_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission034_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_11_coefficients]
def admission034_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(189696976223085150696309260288/10986328125:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/10986328125:ℝ)],
![(379393952446170301392618520576/10986328125:ℝ),(379393952446170301392618520576/3662109375:ℝ),(379393952446170301392618520576/3662109375:ℝ),(379393952446170301392618520576/10986328125:ℝ)],
![(189696976223085150696309260288/10986328125:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/10986328125:ℝ)]]
theorem admission034_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission034_12_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission034_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_12_coefficients]
def admission034_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6675672401954239904317433708544/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(6675672401954239904317433708544/762939453125:ℝ)],
![(13351344803908479808634867417088/762939453125:ℝ),(40054034411725439425904602251264/762939453125:ℝ),(40054034411725439425904602251264/762939453125:ℝ),(13351344803908479808634867417088/762939453125:ℝ)],
![(6675672401954239904317433708544/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(6675672401954239904317433708544/762939453125:ℝ)]]
theorem admission034_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission034_13_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission034_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_13_coefficients]
def admission034_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)],
![(18889465931478580854784/9:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/9:ℝ)],
![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)]]
theorem admission034_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission034_14_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission034_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_14_coefficients]
theorem admission034_all {δ p : ℝ}
 (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission034_00_pos hd hp
 · exact admission034_01_pos hd hp
 · exact admission034_02_pos hd hp
 · exact admission034_03_pos hd hp
 · exact admission034_04_pos hd hp
 · exact admission034_05_pos hd hp
 · exact admission034_06_pos hd hp
 · exact admission034_07_pos hd hp
 · exact admission034_08_pos hd hp
 · exact admission034_09_pos hd hp
 · exact admission034_10_pos hd hp
 · exact admission034_11_pos hd hp
 · exact admission034_12_pos hd hp
 · exact admission034_13_pos hd hp
 · exact admission034_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission034_all
