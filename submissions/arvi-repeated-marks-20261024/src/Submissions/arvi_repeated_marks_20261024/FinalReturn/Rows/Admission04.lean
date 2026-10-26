/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission04_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(16968807097233225562159/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission04_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (25810568996105327810795/14259792031112851124318:ℝ) admission04_00_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission04_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_00_coefficients]
def admission04_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9838911081676800000000/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission04_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (9340336490274451124318/7129896015556425562159:ℝ) admission04_01_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission04_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_01_coefficients]
def admission04_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2352790992103833166404605269/3564948007778212781079500000:ℝ), (0:ℝ)]]
theorem admission04_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (4777105023452592395754394731/7129896015556425562159000000:ℝ) admission04_02_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission04_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_02_coefficients]
def admission04_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3764036785111486460862851584/64169064140007830059431:ℝ), (4971624272121518406003427840/64169064140007830059431:ℝ), (134924144687766541815619584/7129896015556425562159:ℝ)],
![(2546687247765152004369882496/64169064140007830059431:ℝ), (2539868882385549981969882496/64169064140007830059431:ℝ), (0:ℝ)]]
theorem admission04_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (21623657188474022054089039/21903040559789339326952448:ℝ) admission04_03_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission04_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_03_coefficients]
def admission04_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8714656583766586313747031500111/891237001944553195269875000:ℝ), (9728:ℝ), (0:ℝ)],
![(54884314647115878777142707423889/3564948007778212781079500000:ℝ), (2320942872399553189885611051136/111404625243069149408734375:ℝ), (611469443001931826656562525568/111404625243069149408734375:ℝ)]]
theorem admission04_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (272294986336797766558000499667/1825253379982444943912704000000:ℝ) admission04_04_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission04_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_04_coefficients]
def admission04_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(27724329905719957672250848231699/2673711005833659585809625000:ℝ), (6888463791601024703908707701408/334213875729207448226203125:ℝ), (1138306064212445245402239619968/111404625243069149408734375:ℝ)],
![(117646456256400009607486141261/10694844023334638343238500000:ℝ), (471445321714951547608687448/13368555029168297929048125:ℝ), (0:ℝ)]]
theorem admission04_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (697739383382337193686351765839/7301013519929779775650816000000:ℝ) admission04_05_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission04_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_05_coefficients]
def admission04_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(788879380844663849840541121969054624886365747863705609424/264503030080493466816931845894765443820669477703125:ℝ), (1569359225807539774931549153553734229511292040299077547216/264503030080493466816931845894765443820669477703125:ℝ), (780504825542535623751949751882863840226027092435371937792/264503030080493466816931845894765443820669477703125:ℝ), (0:ℝ)],
![(1029322187034836950121271237420812829146003603694535214668/264503030080493466816931845894765443820669477703125:ℝ), (2284087421423917011805880442890468496947143112360228164172/264503030080493466816931845894765443820669477703125:ℝ), (1488707376432051912509250395127457979211729012280526162944/264503030080493466816931845894765443820669477703125:ℝ), (5198151839366100545549771330711341966643286746996293632/5877845112899854818154041019883676529348210615625:ℝ)]]
theorem admission04_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (60730339494909620094977011074348103408073899982145523/288907842989253664021907424209322468770523248179200000:ℝ) admission04_06_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission04_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_06_coefficients]
def admission04_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(831458725416560875717636306990058581017027097897463741/19063281447242772383202295199622734689777980375000:ℝ), (453094804707678106617761394310752859295766854128714208/7148730542716039643700860699858525508666742640625:ℝ), (3156474849522291102201390114923689848973222730781312/158860678727023103193352459996856122414816503125:ℝ)],
![(1783383781336718448370379815489528014062557700064265763/76253125788971089532809180798490938759111921500000:ℝ), (166459872589168472576051172296968781351274809574460616/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission04_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4825132126743710617167229160052619638925212872314141/10411093441054186090879546818353962838577414348800000:ℝ) admission04_07_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission04_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_07_coefficients]
def admission04_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (44403974464057996117225872279800252781068519165215843297848647302397369047/488442528865626716098291012638418085286157123383931699200000000000000:ℝ), (8008280553595881353502087874304110061898823080798105664559797336875841858081/43959827597906404448846191137457627675754141104553852928000000000000000:ℝ), (4011095920175314910173935148117090898005767832139898426352774732165678643851/43959827597906404448846191137457627675754141104553852928000000000000000:ℝ)],
![(3351772689874520556767766976700987765806682349142727068456967796613218665653/6512567051541689547977213501845574470482094978452422656000000000000000:ℝ), (31550281545133249185641271074175165535965941904191291749610277135212696956727/19537701154625068643931640505536723411446284935357267968000000000000000:ℝ), (74126130442534227763859346797018638797565998698377305833909600309718469701889/43959827597906404448846191137457627675754141104553852928000000000000000:ℝ), (25761624810302408445876644696311647920746150845242726013478251293720327542411/43959827597906404448846191137457627675754141104553852928000000000000000:ℝ)]]
theorem admission04_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (27003797322712337287245327364356513759658539315827067285922034729057091628301/1748203906211168936821697183977273624565819705376186249968091136000000000000000:ℝ) admission04_08_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission04_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_08_coefficients]
def admission04_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(35928470252869792235411649438628863294412383200639308231159/35743652713580198218504303499292627543333713203125000:ℝ), (11587759675085353940530893625711247349055720178659818836654/4467956589197524777313037937411578442916714150390625:ℝ), (1079085856665223790507927754420561048064780730921401115904/496439621021947197479226437490175382546301572265625:ℝ), (58114063044370814807030162052654876474094567344040065024/99287924204389439495845287498035076509260314453125:ℝ)],
![(57021637147327129998312462281374476670471978582419743512297/142974610854320792874017213997170510173334852812500000:ℝ), (7110246396698824812995432434102110293934330404122159187401/8935913178395049554626075874823156885833428300781250:ℝ), (197015023789777952497700399920544198442569753587974557888/496439621021947197479226437490175382546301572265625:ℝ), (0:ℝ)]]
theorem admission04_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3094043686793916530726471669116746004643270773920889741/156166401615812791363193202275309442578661215232000000000:ℝ) admission04_09_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission04_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_09_coefficients]
def admission04_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31364042143492506883478723779899436736/626651016992263965424130859375:ℝ), (1778308193315182142938729868491827648/13925578155383643676091796875:ℝ), (7335184274367578757539086995718637568/69627890776918218380458984375:ℝ), (17357171558977378178271662659234930688/626651016992263965424130859375:ℝ)],
![(45126352839571834951188489896927789216/626651016992263965424130859375:ℝ), (35916979101364535642689640840965467872/208883672330754655141376953125:ℝ), (26746944960181024873028545142111126528/208883672330754655141376953125:ℝ), (17616938644776806221341202800364765184/626651016992263965424130859375:ℝ)],
![(1499275857424405779353140556799533708/69627890776918218380458984375:ℝ), (8976569901773293613304675634674259748/208883672330754655141376953125:ℝ), (4478626115433905714733253964275658624/208883672330754655141376953125:ℝ), (0:ℝ)]]
theorem admission04_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (22418795905394871620609238419275123/4672648652755059056416522240000000000:ℝ) admission04_10_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission04_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_10_coefficients]
def admission04_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2093471900724271491260690456185374782856212397803111881/57189844341728317149606885598868204069333941125000:ℝ), (381345241269745411731506284444704131853415369953152848/7148730542716039643700860699858525508666742640625:ℝ), (13374693841617803886496503654689882625455936714781312/794303393635115515966762299984280612074082515625:ℝ)],
![(4449888696373390107245758960569937731191814558876267031/228759377366913268598427542395472816277335764500000:ℝ), (138359688384267785899425123946563109080888459898185964/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission04_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (59383642878648580132542351911251256792180369922316183/156166401615812791363193202275309442578661215232000000:ℝ) admission04_11_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission04_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_11_coefficients]
def admission04_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission04_12_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission04_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_12_coefficients]
def admission04_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (267590012974094731788830531/24597277704192000000000000000:ℝ) admission04_13_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission04_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_13_coefficients]
def admission04_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission04_14_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission04_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_14_coefficients]
theorem admission04_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission04_00_pos hδ hp
 · exact admission04_01_pos hδ hp
 · exact admission04_02_pos hδ hp
 · exact admission04_03_pos hδ hp
 · exact admission04_04_pos hδ hp
 · exact admission04_05_pos hδ hp
 · exact admission04_06_pos hδ hp
 · exact admission04_07_pos hδ hp
 · exact admission04_08_pos hδ hp
 · exact admission04_09_pos hδ hp
 · exact admission04_10_pos hδ hp
 · exact admission04_11_pos hδ hp
 · exact admission04_12_pos hδ hp
 · exact admission04_13_pos hδ hp
 · exact admission04_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
