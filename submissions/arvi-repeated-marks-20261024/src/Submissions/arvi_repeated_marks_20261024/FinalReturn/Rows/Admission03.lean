/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission03_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(16968807097233225562159/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission03_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (25810568996105327810795/14259792031112851124318:ℝ) admission03_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission03_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_00_coefficients]
def admission03_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9838911081676800000000/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission03_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (9340336490274451124318/7129896015556425562159:ℝ) admission03_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission03_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_01_coefficients]
def admission03_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2352790992103833166404605269/3564948007778212781079500000:ℝ), (0:ℝ)]]
theorem admission03_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (4777105023452592395754394731/7129896015556425562159000000:ℝ) admission03_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission03_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_02_coefficients]
def admission03_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(942691650072838348015712896/64169064140007830059431:ℝ), (1242906068030379601500856960/64169064140007830059431:ℝ), (33731036171941635453904896/7129896015556425562159:ℝ)],
![(637640482047013384454372416/64169064140007830059431:ℝ), (634187024257344827654372416/64169064140007830059431:ℝ), (0:ℝ)]]
theorem admission03_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (10737712547960772081955373/10951520279894669663476224:ℝ) admission03_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission03_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_03_coefficients]
def admission03_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4379679806308279571954359500111/1782474003889106390539750000:ℝ), (2432:ℝ), (0:ℝ)],
![(2776324924024384641663342362007/712989601555642556215900000:ℝ), (583800666107666510252482262784/111404625243069149408734375:ℝ), (152867360750482956664140631392/111404625243069149408734375:ℝ)]]
theorem admission03_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (272294986336797766558000499667/1825253379982444943912704000000:ℝ) admission03_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission03_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_04_coefficients]
def admission03_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9357392056930567308517936473813/3564948007778212781079500000:ℝ), (5593147263493079427660570899141/1069484402333463834323850000:ℝ), (5546245338431996842464354913861/2138968804666927668647700000:ℝ)],
![(0:ℝ), (271660590098875706208681253273/5347422011667319171619250000:ℝ), (411881151061298322668023690073/10694844023334638343238500000:ℝ)]]
theorem admission03_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (343171010370146001899917204979879/3738118922204047245133217792000000:ℝ) admission03_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission03_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_05_coefficients]
def admission03_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(99662987163263934156376991581451735093613250411504910132/264503030080493466816931845894765443820669477703125:ℝ), (197213600066251037794899850417717597321316236965926402356/264503030080493466816931845894765443820669477703125:ℝ), (97563103192816952968993718985357980028253386554421492224/264503030080493466816931845894765443820669477703125:ℝ), (0:ℝ)],
![(130552729171193172620549159440740041819382562221193611506/264503030080493466816931845894765443820669477703125:ℝ), (288195234718984458559567564669541557233496276929487053298/264503030080493466816931845894765443820669477703125:ℝ), (186894928625893078452166488590752619087573402660147593472/264503030080493466816931845894765443820669477703125:ℝ), (649768979920762568193721416338917745830410843374536704/5877845112899854818154041019883676529348210615625:ℝ)]]
theorem admission03_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (60730339494909620094977011074348103408073899982145523/288907842989253664021907424209322468770523248179200000:ℝ) admission03_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission03_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_06_coefficients]
def admission03_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1250162430332982599078113564413428478683193968718170551/114379688683456634299213771197736408138667882250000:ℝ), (113273701176919526654440348577688214823941713532178552/7148730542716039643700860699858525508666742640625:ℝ), (789118712380572775550347528730922462243305682695328/158860678727023103193352459996856122414816503125:ℝ)],
![(1322799467745519382530594002262754928831248392646358651/228759377366913268598427542395472816277335764500000:ℝ), (40976919231916259433116515156579197453593202697631276/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission03_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (2375576123729015959729692039617047829044951482280727/5205546720527093045439773409176981419288707174400000:ℝ) admission03_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission03_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_07_coefficients]
def admission03_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (990686651667073791853498528571726096723130472846143532677590892460983088747/87919655195812808897692382274915255351508282209107705856000000000000000:ℝ), (3980792551699777598148897641241958188989677093810172025859337434771447784609/175839310391625617795384764549830510703016564418215411712000000000000000:ℝ), (44394786334554142864138936490855848185547535567562717282285932330237369047/3907540230925013728786328101107344682289256987071453593600000000000000:ℝ)],
![(22718640620130768388310240958685450221880197910646292066650636920959608677/339786107036957715546637226183247363677326694527952486400000000000000:ℝ), (72710036820434554201663212714860859334953778698620178373954562551188587429059/351678620783251235590769529099661021406033128836430823424000000000000000:ℝ), (37472849105447483704952092241664651390546278191735130814520925565282102280577/175839310391625617795384764549830510703016564418215411712000000000000000:ℝ), (286067329558188515483057931470795370660440680157594134917013449680844579031/3907540230925013728786328101107344682289256987071453593600000000000000:ℝ)]]
theorem admission03_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1252248351411035121947809705913942703308193113003783210522994339833613289/82419251733370981830252879286513685809808157927635810632335360000000000000:ℝ) admission03_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission03_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_08_coefficients]
def admission03_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1800195394500480940486154903070794552671111128517050594163/14297461085432079287401721399717051017333485281250000:ℝ), (2899343110296684912717039887240201039237038448044956591319/8935913178395049554626075874823156885833428300781250:ℝ), (134885732083152973813490969302570131008097591365175139488/496439621021947197479226437490175382546301572265625:ℝ), (7264257880546351850878770256581859559261820918005008128/99287924204389439495845287498035076509260314453125:ℝ)],
![(1356665017916496266917462348321341769097653688906668788743/28594922170864158574803442799434102034666970562500000:ℝ), (1687989003384481842077281399606116805495381239171408351899/17871826356790099109252151749646313771666856601562500:ℝ), (23331892072486792074115684526293811991472160801893621904/496439621021947197479226437490175382546301572265625:ℝ), (0:ℝ)]]
theorem admission03_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1419329810340479424234507451141895002256486191136138087/78083200807906395681596601137654721289330607616000000000:ℝ) admission03_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission03_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_09_coefficients]
def admission03_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1980303545669454470646908128620676952/626651016992263965424130859375:ℝ), (1684692424876674872766786055050485576/208883672330754655141376953125:ℝ), (18554433257418470263072334273571456/2785115631076728735218359375:ℝ), (1101058665298550388833825175022797824/626651016992263965424130859375:ℝ)],
![(2828468913514970023886420181454139384/626651016992263965424130859375:ℝ), (2258770567163107618766869857322236968/208883672330754655141376953125:ℝ), (564577560811112154628411898130733184/69627890776918218380458984375:ℝ), (1133529551023478894217517692664027136/626651016992263965424130859375:ℝ)],
![(90379245319193963198800732222574038/69627890776918218380458984375:ℝ), (180032372483980246934465930171134326/69627890776918218380458984375:ℝ), (89643189480261326039665197948560288/69627890776918218380458984375:ℝ), (0:ℝ)]]
theorem admission03_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5059145212598222474719852850012427/1168162163188764764104130560000000000:ℝ) admission03_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission03_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_10_coefficients]
def admission03_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(349859971314510261416179816658464676652988213240875907/38126562894485544766404590399245469379555960750000:ℝ), (95336310317436352932876571111176032963353842488288212/7148730542716039643700860699858525508666742640625:ℝ), (3343673460404450971624125913672470656363984178695328/794303393635115515966762299984280612074082515625:ℝ)],
![(366650603644841948061875446870603825004165788174763543/76253125788971089532809180798490938759111921500000:ℝ), (34029656161977657506070257308209993391642102677320674/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission03_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (29221617358954914148386533249015437210038999686029061/78083200807906395681596601137654721289330607616000000:ℝ) admission03_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission03_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_11_coefficients]
def admission03_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission03_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission03_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_12_coefficients]
def admission03_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (267590012974094731788830531/24597277704192000000000000000:ℝ) admission03_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission03_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_13_coefficients]
def admission03_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission03_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission03_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_14_coefficients]
theorem admission03_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission03_00_pos hδ hp
 · exact admission03_01_pos hδ hp
 · exact admission03_02_pos hδ hp
 · exact admission03_03_pos hδ hp
 · exact admission03_04_pos hδ hp
 · exact admission03_05_pos hδ hp
 · exact admission03_06_pos hδ hp
 · exact admission03_07_pos hδ hp
 · exact admission03_08_pos hδ hp
 · exact admission03_09_pos hδ hp
 · exact admission03_10_pos hδ hp
 · exact admission03_11_pos hδ hp
 · exact admission03_12_pos hδ hp
 · exact admission03_13_pos hδ hp
 · exact admission03_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
