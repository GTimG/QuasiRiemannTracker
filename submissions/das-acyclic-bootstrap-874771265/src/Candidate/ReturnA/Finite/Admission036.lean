/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission036_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4157056650039672445075456/70916363469:ℝ),(12451511126481951262769152/70916363469:ℝ),(12431852302844885190311936/70916363469:ℝ),(4137397826402606372618240/70916363469:ℝ)],
![(8314113300079344890150912/70916363469:ℝ),(24903022252963902525538304/70916363469:ℝ),(24863704605689770380623872/70916363469:ℝ),(8274795652805212745236480/70916363469:ℝ)],
![(4157056650039672445075456/70916363469:ℝ),(12451511126481951262769152/70916363469:ℝ),(12431852302844885190311936/70916363469:ℝ),(4137397826402606372618240/70916363469:ℝ)]]
theorem admission036_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission036_00_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission036_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_00_coefficients]
def admission036_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3039438400689189098094592/70916363469:ℝ),(9107320085789807294283776/70916363469:ℝ),(9096324969512047294283776/70916363469:ℝ),(1009481094803809699364864/23638787823:ℝ)],
![(6078876801378378196189184/70916363469:ℝ),(18214640171579614588567552/70916363469:ℝ),(18192649939024094588567552/70916363469:ℝ),(2018962189607619398729728/23638787823:ℝ)],
![(3039438400689189098094592/70916363469:ℝ),(9107320085789807294283776/70916363469:ℝ),(9096324969512047294283776/70916363469:ℝ),(1009481094803809699364864/23638787823:ℝ)]]
theorem admission036_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission036_01_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission036_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_01_coefficients]
def admission036_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(107349722056205484412633088/4924747463125:ℝ),(2895135049226342392263606272/44322727168125:ℝ),(2891827602935136705386119168/44322727168125:ℝ),(962840052214643672836210688/44322727168125:ℝ)],
![(214699444112410968825266176/4924747463125:ℝ),(5790270098452684784527212544/44322727168125:ℝ),(5783655205870273410772238336/44322727168125:ℝ),(1925680104429287345672421376/44322727168125:ℝ)],
![(107349722056205484412633088/4924747463125:ℝ),(2895135049226342392263606272/44322727168125:ℝ),(2891827602935136705386119168/44322727168125:ℝ),(962840052214643672836210688/44322727168125:ℝ)]]
theorem admission036_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission036_02_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission036_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_02_coefficients]
def admission036_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6792843866537758849761280/212749090407:ℝ),(20332532289394906482343936/212749090407:ℝ),(20286562517562456415404032/212749090407:ℝ),(6746874094705308782821376/212749090407:ℝ)],
![(1937517474652370147213312/30392727201:ℝ),(5799411200566957376012288/30392727201:ℝ),(40503949011381310172692480/212749090407:ℝ),(13470692929979199571099648/212749090407:ℝ)],
![(6769778456028832180731904/212749090407:ℝ),(20263346114573795149742080/212749090407:ℝ),(20217386493818853757288448/212749090407:ℝ),(6723818835273890788278272/212749090407:ℝ)]]
theorem admission036_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (48922220850901/96824474923008:ℝ) admission036_03_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission036_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_03_coefficients]
def admission036_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10629277891929110365503488/2110606055625:ℝ),(222385303688497776475602944/14774242389375:ℝ),(221556758919404030674337792/14774242389375:ℝ),(73576400474410026757259264/14774242389375:ℝ)],
![(149282674339141455019016192/14774242389375:ℝ),(29745753911418814894669824/984949492625:ℝ),(148175524008402084465475584/4924747463125:ℝ),(147622937693065484995395584/14774242389375:ℝ)],
![(24959243031879227486830592/4924747463125:ℝ),(223801004982784446944444416/14774242389375:ℝ),(6370566088737206363488256/422121211125:ℝ),(705205116368147221315584/140707070375:ℝ)]]
theorem admission036_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (205570088162301183/2581985997946880000:ℝ) admission036_04_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission036_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_04_coefficients]
def admission036_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14577022736130574208073728/4924747463125:ℝ),(393673370913322235607842816/44322727168125:ℝ),(11250448684987901182902272/1266363633375:ℝ),(18755076812347067666628608/6331818166875:ℝ)],
![(86589071586442537111027712/14774242389375:ℝ),(779497632717160351055577088/44322727168125:ℝ),(779690768653807193271762944/44322727168125:ℝ),(259960350695974453549268992/44322727168125:ℝ)],
![(42858003378050814486806528/14774242389375:ℝ),(55117751686262587921104896/6331818166875:ℝ),(385925064679230651870183424/44322727168125:ℝ),(128674813009544979882868736/44322727168125:ℝ)]]
theorem admission036_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (3923767399113538923963/84606517180723363840000:ℝ) admission036_05_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission036_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_05_coefficients]
def admission036_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8075368035653407711506548991209537536/1107606145736254496527125:ℝ),(3253604256554491290288139540340965376/149676506180574931963125:ℝ),(119638059890369776888579199941803507712/5538030728681272482635625:ℝ),(7926308257346000100209516381047095296/1107606145736254496527125:ℝ)],
![(113384680874967547722246662432088031232/7753243020153781475689875:ℝ),(1690299398310026375217849487917110296576/38766215100768907378449375:ℝ),(1679854727531103912709858459685513854976/38766215100768907378449375:ℝ),(111295743103122028581590536785768742912/7753243020153781475689875:ℝ)],
![(11371420925078738748340163898724253696/1550648604030756295137975:ℝ),(847615895862413131033221346968800264192/38766215100768907378449375:ℝ),(842388308298515474489804060092889300992/38766215100768907378449375:ℝ),(11162317060340005576024784423687815168/1550648604030756295137975:ℝ)]]
theorem admission036_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (7381949813427403662548881379/64522734548418821941690368000:ℝ) admission036_06_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission036_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_06_coefficients]
def admission036_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3221515319033326888839188733613735936/209547108652804904748375:ℝ),(48192180768244482032959035426359246848/1047735543264024523741875:ℝ),(5340195736851169461767377617443356672/116415060362669391526875:ℝ),(3195431491716535513428661359739928576/209547108652804904748375:ℝ)],
![(916864396719328980850465609028501504/29935301236114986392625:ℝ),(96010173799549008158906542759819968512/1047735543264024523741875:ℝ),(10638871688593859025722525994469818368/116415060362669391526875:ℝ),(129918062379478520009642806148595712/4276471605159283770375:ℝ)],
![(3196535458001975977114070529585774592/209547108652804904748375:ℝ),(47817993031304526125947507333460721664/1047735543264024523741875:ℝ),(5298675951742689563955148377026461696/116415060362669391526875:ℝ),(3170553564877911967043836141541261312/209547108652804904748375:ℝ)]]
theorem admission036_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1476404054499190285356639019/6103501916742320994484224000:ℝ) admission036_07_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission036_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_07_coefficients]
def admission036_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6936917784570831476514745597432473150059976/47369409327258053192901611328125:ℝ),(572846545421767919194339161143211114443705864/1278974051835967436208343505859375:ℝ),(5559978119067617061462305919653445098309368/12180705255580642249603271484375:ℝ),(198247882694293944531850636646061763742897128/1278974051835967436208343505859375:ℝ)],
![(15017445669162416369893995020748444166505376/47369409327258053192901611328125:ℝ),(176862595631928575399914632325547252068954144/182710578833709633744049072265625:ℝ),(419884575065606104356539203865345247726979024/426324683945322478736114501953125:ℝ),(427086479527459480129659647601231497131403216/1278974051835967436208343505859375:ℝ)],
![(323221115383663395735169976932638840657816/1894776373090322127716064453125:ℝ),(665191624001732108605063265135619650038973144/1278974051835967436208343505859375:ℝ),(225285340898239507205358496677474669286151144/426324683945322478736114501953125:ℝ),(32691228119023647942544144422167104769786584/182710578833709633744049072265625:ℝ)]]
theorem admission036_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (7804032507642185411079088797111532293817473/3333325846796872905787650867200000000000000000:ℝ) admission036_08_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission036_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_08_coefficients]
def admission036_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(42697529896123276999096819059469808666048/75791054923612885108642578125:ℝ),(684940739489542987686801575810392597426688/409271696587509579586669921875:ℝ),(3390944432731830031609506747775715707715584/2046358482937547897933349609375:ℝ),(24868313671050238913115684147471142879232/45474632954167731065185546875:ℝ)],
![(83387212066303942548384216266581310930752/75791054923612885108642578125:ℝ),(267489798559438803101577617065156376473088/81854339317501915917333984375:ℝ),(6620198754334223778482791202333654683222016/2046358482937547897933349609375:ℝ),(48542414706809328936206957198282206478336/45474632954167731065185546875:ℝ)],
![(5812811738597237935612485315301643180672/10827293560516126444091796875:ℝ),(652508253307651027821086509515389284938752/409271696587509579586669921875:ℝ),(3229254321602393746873284454557938975506432/2046358482937547897933349609375:ℝ),(7891367011919696674363757683603687866368/15158210984722577021728515625:ℝ)]]
theorem admission036_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (2116629573919691743531042908204591/254312579864263374770176000000000000:ℝ) admission036_09_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission036_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_09_coefficients]
def admission036_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12985192012300623756352283691152/86567826500244140625:ℝ),(38490151506268659707215115402128/86567826500244140625:ℝ),(1521003982801955242479981439232/3462713060009765625:ℝ),(1391126756442017729362411585536/9618647388916015625:ℝ)],
![(337224310108669989529681926592/1154237686669921875:ℝ),(24983152936582785710720474339264/28855942166748046875:ℝ),(24674727967923635528921179184128/28855942166748046875:ℝ),(2707394424516009747980917669888/9618647388916015625:ℝ)],
![(12304209880726638075946587985984/86567826500244140625:ℝ),(7290412683204188671593107580736/17313565300048828125:ℝ),(35991860621200637963410936849408/86567826500244140625:ℝ),(1316000869165308665987998547968/9618647388916015625:ℝ)]]
theorem admission036_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (90362608508970474196563621/41311775967150080000000000000:ℝ) admission036_10_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission036_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_10_coefficients]
def admission036_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13213958737918602369873595847788691456/1047735543264024523741875:ℝ),(105426865550261647358597366920019968/2793961448704065396645:ℝ),(1577135895525248605097742920700657664/41909421730560980949675:ℝ),(4369093848233899912614385423432548352/349245181088008174580625:ℝ)],
![(3760415906863333225415443949596278784/149676506180574931963125:ℝ),(26251856006803522484036609357057327104/349245181088008174580625:ℝ),(78542650350121117371578729260931612672/1047735543264024523741875:ℝ),(1243333032273994404637000420806361088/49892168726858310654375:ℝ)],
![(13108952610124730208034511799385260032/1047735543264024523741875:ℝ),(13073497813020816564211938492054831104/349245181088008174580625:ℝ),(39114252961989902244135156243415171072/1047735543264024523741875:ℝ),(4334237377684060919844617522211979264/349245181088008174580625:ℝ)]]
theorem admission036_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (2018286556789679881112937593/10172503194570534990807040000:ℝ) admission036_11_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission036_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_11_coefficients]
def admission036_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5653410441371355971584/10986328125:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/10986328125:ℝ)],
![(11306820882742711943168/10986328125:ℝ),(11306820882742711943168/3662109375:ℝ),(11306820882742711943168/3662109375:ℝ),(11306820882742711943168/10986328125:ℝ)],
![(5653410441371355971584/10986328125:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/10986328125:ℝ)]]
theorem admission036_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission036_12_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission036_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_12_coefficients]
def admission036_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(198950541077680584916992/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(198950541077680584916992/762939453125:ℝ)],
![(397901082155361169833984/762939453125:ℝ),(1193703246466083509501952/762939453125:ℝ),(1193703246466083509501952/762939453125:ℝ),(397901082155361169833984/762939453125:ℝ)],
![(198950541077680584916992/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(198950541077680584916992/762939453125:ℝ)]]
theorem admission036_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission036_13_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission036_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_13_coefficients]
def admission036_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)],
![(562949953421312/9:ℝ),(562949953421312/3:ℝ),(562949953421312/3:ℝ),(562949953421312/9:ℝ)],
![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)]]
theorem admission036_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission036_14_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission036_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_14_coefficients]
theorem admission036_all {δ p : ℝ}
 (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission036_00_pos hd hp
 · exact admission036_01_pos hd hp
 · exact admission036_02_pos hd hp
 · exact admission036_03_pos hd hp
 · exact admission036_04_pos hd hp
 · exact admission036_05_pos hd hp
 · exact admission036_06_pos hd hp
 · exact admission036_07_pos hd hp
 · exact admission036_08_pos hd hp
 · exact admission036_09_pos hd hp
 · exact admission036_10_pos hd hp
 · exact admission036_11_pos hd hp
 · exact admission036_12_pos hd hp
 · exact admission036_13_pos hd hp
 · exact admission036_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission036_all
