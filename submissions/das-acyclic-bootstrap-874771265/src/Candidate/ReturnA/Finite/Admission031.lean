/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission031_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4339664423883818141899099734016/70916363469:ℝ),(13017704910985575663572743094272/70916363469:ℝ),(13016416550319696901448186986496/70916363469:ℝ),(4338376063217939379774543626240/70916363469:ℝ)],
![(8679328847767636283798199468032/70916363469:ℝ),(26035409821971151327145486188544/70916363469:ℝ),(26032833100639393802896373972992/70916363469:ℝ),(8676752126435878759549087252480/70916363469:ℝ)],
![(4339664423883818141899099734016/70916363469:ℝ),(13017704910985575663572743094272/70916363469:ℝ),(13016416550319696901448186986496/70916363469:ℝ),(4338376063217939379774543626240/70916363469:ℝ)]]
theorem admission031_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission031_00_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission031_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_00_coefficients]
def admission031_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3176273521335377957323634900992/70916363469:ℝ),(9528099988065754592610904702976/70916363469:ℝ),(9527379412125375313250904702976/70916363469:ℝ),(1058517648464999559321211633664/23638787823:ℝ)],
![(6352547042670755914647269801984/70916363469:ℝ),(19056199976131509185221809405952/70916363469:ℝ),(19054758824250750626501809405952/70916363469:ℝ),(2117035296929999118642423267328/23638787823:ℝ)],
![(3176273521335377957323634900992/70916363469:ℝ),(9528099988065754592610904702976/70916363469:ℝ),(9527379412125375313250904702976/70916363469:ℝ),(1058517648464999559321211633664/23638787823:ℝ)]]
theorem admission031_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission031_01_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission031_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_01_coefficients]
def admission031_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(336609242463720886594368484409344/14774242389375:ℝ),(3029266425373347523454113364836352/44322727168125:ℝ),(3029049668573207067558910369988608/44322727168125:ℝ),(1009610970591022203887902458380288/44322727168125:ℝ)],
![(673218484927441773188736968818688/14774242389375:ℝ),(6058532850746695046908226729672704/44322727168125:ℝ),(6058099337146414135117820739977216/44322727168125:ℝ),(2019221941182044407775804916760576/44322727168125:ℝ)],
![(336609242463720886594368484409344/14774242389375:ℝ),(3029266425373347523454113364836352/44322727168125:ℝ),(3029049668573207067558910369988608/44322727168125:ℝ),(1009610970591022203887902458380288/44322727168125:ℝ)]]
theorem admission031_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission031_02_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission031_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_02_coefficients]
def admission031_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7069311056471363996268391038976/212749090407:ℝ),(21204922020628314137335416487936/212749090407:ℝ),(21201910992735128250025659858944/212749090407:ℝ),(7066300028578178108958634409984/212749090407:ℝ)],
![(14137111121519429241715709444096/212749090407:ℝ),(42405311108903774172298310844416/212749090407:ℝ),(6057041299294086248401356193792/30392727201:ℝ),(2018727015382036972603841708032/30392727201:ℝ)],
![(7067800065048065245447318405120/212749090407:ℝ),(21200389088275460034962894356480/212749090407:ℝ),(21197378102323475488783833497600/212749090407:ℝ),(7064789079096080699268257546240/212749090407:ℝ)]]
theorem admission031_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1568698299946565/3098383197536256:ℝ) admission031_03_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission031_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_03_coefficients]
def admission031_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25714340490228547322791933771776/4924747463125:ℝ),(77124954947081521165170810814464/4924747463125:ℝ),(77106889770357384183031667884032/4924747463125:ℝ),(25696275313504410340652790841344/4924747463125:ℝ)],
![(154316864653483833671561821290496/14774242389375:ℝ),(462842183987577613053487172550656/14774242389375:ℝ),(13220965202765460286382081572864/422121211125:ℝ),(4405956078934209446898500108288/422121211125:ℝ)],
![(77173843182798191703186019975168/14774242389375:ℝ),(231467319146333049557974740107264/14774242389375:ℝ),(231413112785718957474277851398144/14774242389375:ℝ),(77119636822184099619489131266048/14774242389375:ℝ)]]
theorem admission031_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (821623579204596741/10327943991787520000:ℝ) admission031_04_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission031_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_04_coefficients]
def admission031_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6507908980992776450224452272128/2110606055625:ℝ),(410004096581322444200841203154944/44322727168125:ℝ),(410009921532150686782029285031936/44322727168125:ℝ),(27334382710335309607180315918336/8864545433625:ℝ)],
![(13007668860684927166208297402368/2110606055625:ℝ),(819494834456758963509526049849344/44322727168125:ℝ),(819506519033304286906357441888256/44322727168125:ℝ),(54634546130185758777441127497728/8864545433625:ℝ)],
![(433317325312810047732256342016/140707070375:ℝ),(2339947073573922967478199123968/253272726675:ℝ),(11699902785747245717837947338752/1266363633375:ℝ),(3900023345692921310037258797056/1266363633375:ℝ)]]
theorem admission031_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (929798109010527236363961/19802759678413879902208000:ℝ) admission031_05_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission031_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_05_coefficients]
def admission031_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(58204626566782509087809465260416370456133632/7753243020153781475689875:ℝ),(872728410684007356941370238117341255352451072/38766215100768907378449375:ℝ),(872387476219740725152504280778349705840033792/38766215100768907378449375:ℝ),(58136439673467434229180086339178060553650176/7753243020153781475689875:ℝ)],
![(116430720006045422621385555832266705606803456/7753243020153781475689875:ℝ),(1745778781528995437774685307125824318636818432/38766215100768907378449375:ℝ),(1745096869681351717293420030713050927204401152/38766215100768907378449375:ℝ),(930354701084744713980325263835776218562560/62025944161230251805519:ℝ)],
![(58226093439262913533576090571850335150669824/7753243020153781475689875:ℝ),(174610074168997616166663013801696612656873472/7753243020153781475689875:ℝ),(174541878692322198428183149986940244272873472/7753243020153781475689875:ℝ),(58157897962125655018360571640293966766669824/7753243020153781475689875:ℝ)]]
theorem admission031_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (206542124464687881261611175671/1806636567355727014367330304000:ℝ) admission031_06_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission031_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_06_coefficients]
def admission031_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3343395075148940879255351245467742231330816/209547108652804904748375:ℝ),(50142378083403579015642137466355112659124224/1047735543264024523741875:ℝ),(1856808539706815682658283478056418968338432/38805020120889797175625:ℝ),(3341685572885029762481654533701382128533504/209547108652804904748375:ℝ)],
![(6685159333351943517769974528435131374370816/209547108652804904748375:ℝ),(100260295998411232527958809707897178998964224/1047735543264024523741875:ℝ),(3712711224497604903712818625008740893458432/38805020120889797175625:ℝ),(6681740745956763492227433161902896399253504/209547108652804904748375:ℝ)],
![(26734114065624021108116986263739113144320/1676376869222439237987:ℝ),(80188668664012245619706675586467306143744/1676376869222439237987:ℝ),(2969444295665262753687256235123715080192/62088032193423675481:ℝ),(26720441384573869837966229025612114165760/1676376869222439237987:ℝ)]]
theorem admission031_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (379720310442250334943512215/1562496490686034174587961344:ℝ) admission031_07_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission031_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_07_coefficients]
def admission031_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1345345728235645498715553676714079104736013483008/8700503753986173035430908203125:ℝ),(84859936031143474472192099890148272032392746351616/182710578833709633744049072265625:ℝ),(7929888218468222291367610318924627843773355437056/17052987357812899149444580078125:ℝ),(28355412314827659647490404195486423152003773617152/182710578833709633744049072265625:ℝ)],
![(540867495885570980053679336794190164699321743872/1740100750797234607086181640625:ℝ),(170579404011200205175289201026164600063778330519552/182710578833709633744049072265625:ℝ),(398499594693273040563054910689532404199796430444544/426324683945322478736114501953125:ℝ),(398980565449392323656964306755531624026747459442688/1278974051835967436208343505859375:ℝ)],
![(1358991751192209401552843007256871718760595236352/8700503753986173035430908203125:ℝ),(85719467980056730703097101136016328031385584167936/182710578833709633744049072265625:ℝ),(200252389231567483278864652716416708105462544518144/426324683945322478736114501953125:ℝ),(200492679245598706124531477387126661962721044122624/1278974051835967436208343505859375:ℝ)]]
theorem admission031_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1313814187730122557339407887416092875718763167/557277659937958833555355834777600000000000000000:ℝ) admission031_08_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission031_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_08_coefficients]
def admission031_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(385427275601353958176605266256125352044768055296/682119494312515965977783203125:ℝ),(693325487965650572589698157269450038487201349632/409271696587509579586669921875:ℝ),(3464409552404228903794859940638021234197352415232/2046358482937547897933349609375:ℝ),(8548621773323250427815890896549922953123332096/15158210984722577021728515625:ℝ)],
![(769679948710221469690612234188829966872864480256/682119494312515965977783203125:ℝ),(1384537077713738971950549889902020295769277464576/409271696587509579586669921875:ℝ),(6918251544831112731214021839362885093318482460672/2046358482937547897933349609375:ℝ),(7316209531524723119034100796238403251862503424/6496376136309675866455078125:ℝ)],
![(76850534621773502302801393586540922965619284992/136423898862503193195556640625:ℝ),(691211589748088399360851732632570257282076114944/409271696587509579586669921875:ℝ),(690768398485376765483832379744972771824226009088/409271696587509579586669921875:ℝ),(5113520280140662109958206576803810780733505536/9094926590833546213037109375:ℝ)]]
theorem admission031_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (13952158806589055829931221278831283/1627600511131285598529126400000000000:ℝ) admission031_09_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission031_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_09_coefficients]
def admission031_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(204994212388986106625332857617190912/1374092484130859375:ℝ),(4301485676196802042191852469035372544/9618647388916015625:ℝ),(4298093063769950779254722344109735936/9618647388916015625:ℝ),(1431566874316836652971449878394699776/9618647388916015625:ℝ)],
![(736719315802526979405788224344905728/2473366471435546875:ℝ),(15458895550657329594599168971097544704/17313565300048828125:ℝ),(3089337217311569234279885389390413824/3462713060009765625:ℝ),(571647305177005221812516727363207168/1923729477783203125:ℝ)],
![(73545890469431279934118711870800128/494673294287109375:ℝ),(220463298007870262658851235075718912/494673294287109375:ℝ),(44057786683289618375415081407807488/98934658857421875:ℝ),(8152391764342054223307195426013184/54963699365234375:ℝ)]]
theorem admission031_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (546660467081356704307830027/241732906230638182400000000000:ℝ) admission031_10_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission031_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_10_coefficients]
def admission031_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13713279715811718046677731832928999533707264/1047735543264024523741875:ℝ),(1523438812559623874370231845437448497659904/38805020120889797175625:ℝ),(41125857241025010969829521521788278305456128/1047735543264024523741875:ℝ),(4568763005908961469503664509302056134115328/349245181088008174580625:ℝ)],
![(27419704583888060187856220372820205527629824/1047735543264024523741875:ℝ),(9138348124657940252019083639371328254902272/116415060362669391526875:ℝ),(82231153512525308152647040909810911923929088/1047735543264024523741875:ℝ),(9135241658163968690777169509429721052479488/349245181088008174580625:ℝ)],
![(2741284973615268428235697707978241198784512/209547108652804904748375:ℝ),(913606337395813725781677620611796552384512/23283012072533878305375:ℝ),(8221059254300059436563503877604526723694592/209547108652804904748375:ℝ),(913295730451001444254701000025532983672832/69849036217601634916125:ℝ)]]
theorem admission031_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (12978712937453472083215913813/65104020445251423941165056000:ℝ) admission031_11_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission031_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_11_coefficients]
def admission031_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5928030506971410959259664384/10986328125:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/10986328125:ℝ)],
![(11856061013942821918519328768/10986328125:ℝ),(11856061013942821918519328768/3662109375:ℝ),(11856061013942821918519328768/3662109375:ℝ),(11856061013942821918519328768/10986328125:ℝ)],
![(5928030506971410959259664384/10986328125:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/10986328125:ℝ)]]
theorem admission031_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission031_12_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission031_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_12_coefficients]
def admission031_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(208614762561069997009919803392/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(208614762561069997009919803392/762939453125:ℝ)],
![(417229525122139994019839606784/762939453125:ℝ),(1251688575366419982059518820352/762939453125:ℝ),(1251688575366419982059518820352/762939453125:ℝ),(417229525122139994019839606784/762939453125:ℝ)],
![(208614762561069997009919803392/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(208614762561069997009919803392/762939453125:ℝ)]]
theorem admission031_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission031_13_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission031_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_13_coefficients]
def admission031_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)],
![(590295810358705651712/9:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/9:ℝ)],
![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)]]
theorem admission031_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission031_14_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission031_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_14_coefficients]
theorem admission031_all {δ p : ℝ}
 (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission031_00_pos hd hp
 · exact admission031_01_pos hd hp
 · exact admission031_02_pos hd hp
 · exact admission031_03_pos hd hp
 · exact admission031_04_pos hd hp
 · exact admission031_05_pos hd hp
 · exact admission031_06_pos hd hp
 · exact admission031_07_pos hd hp
 · exact admission031_08_pos hd hp
 · exact admission031_09_pos hd hp
 · exact admission031_10_pos hd hp
 · exact admission031_11_pos hd hp
 · exact admission031_12_pos hd hp
 · exact admission031_13_pos hd hp
 · exact admission031_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission031_all
