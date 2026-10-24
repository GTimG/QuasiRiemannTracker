/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def admission30_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(69876031193863/1109580632023:ℝ), (202299351685520/3328741896069:ℝ)]]
theorem admission30_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (12643709480345/13314967584276:ℝ) admission30_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission30_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_00_coefficients]
def admission30_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(51013160449472/1109580632023:ℝ), (149039481348416/3328741896069:ℝ)]]
theorem admission30_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2328741896069/3328741896069:ℝ) admission30_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission30_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_01_coefficients]
def admission30_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(25813175179036/1109580632023:ℝ), (75500844527968/3328741896069:ℝ)]]
theorem admission30_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2359401391499/6657483792138:ℝ) admission30_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission30_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_02_coefficients]
def admission30_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1875982681339607488/9986225688207:ℝ), (10968611251357093184/29958677064621:ℝ), (5342139207338270720/29958677064621:ℝ)],
![(1826798429155308928/9986225688207:ℝ), (10673820382919166080/29958677064621:ℝ), (5194937095453239296/29958677064621:ℝ)]]
theorem admission30_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2536590378639277/5112947552361984:ℝ) admission30_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission30_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_03_coefficients]
def admission30_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(107871212677353812/3328741896069:ℝ), (206848834776673088/3328741896069:ℝ), (99057108020694016/3328741896069:ℝ)],
![(112918244889501320/3328741896069:ℝ), (216725982357601408/3328741896069:ℝ), (103889162070483968/3328741896069:ℝ)]]
theorem admission30_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (96735457051459/1136210567191552:ℝ) admission30_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission30_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_04_coefficients]
def admission30_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19262100705073624672/1248278211025875:ℝ), (194339722574869776548/6241391055129375:ℝ), (32652342398974671896/2080463685043125:ℝ)],
![(15833070547911282904/1248278211025875:ℝ), (160472521272579596696/6241391055129375:ℝ), (27077738634517802392/2080463685043125:ℝ)]]
theorem admission30_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1979133818488910363/54538107225194496000:ℝ) admission30_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission30_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_05_coefficients]
def admission30_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3915510238504649043771128715456896/1229938009781599572939456471:ℝ), (1248301485303298118182130379953536/136659778864622174771050719:ℝ), (10732519502497448567195947815866368/1229938009781599572939456471:ℝ), (1137755297632744808018634370580480/409979336593866524313152157:ℝ)],
![(4079419817978909083766132723631872/1229938009781599572939456471:ℝ), (3906152519909599708229817371151616/409979336593866524313152157:ℝ), (11208438525076547939154841547677696/1229938009781599572939456471:ℝ), (396594341302648803929724684206080/136659778864622174771050719:ℝ)]]
theorem admission30_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (8680384045659979309224200215/69969806778686553482777968128:ℝ) admission30_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission30_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_06_coefficients]
def admission30_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9069634558627824868382029771324/99724703495805370778874849:ℝ), (652559127012529927870485581632/3693507536881680399217587:ℝ), (8553312263841613346165149081600/99724703495805370778874849:ℝ)],
![(8502631535355807960915238303768/99724703495805370778874849:ℝ), (1833596165612342924780520936832/11080522610645041197652761:ℝ), (8003456475451795345340246640640/99724703495805370778874849:ℝ)]]
theorem admission30_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3907937732154196945966917305/17019682729950783279594640896:ℝ) admission30_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission30_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_07_coefficients]
def admission30_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1132569302752551728723039140019781187336630697447/12465587936975671347359356125000000000000000:ℝ), (18077224095803498591442513137858886161909629611517/62327939684878356736796780625000000000000000:ℝ), (19170150488729986098386491635714457293405693266167/62327939684878356736796780625000000000000000:ℝ), (1351057810887382212102283705549545383860843428377/12465587936975671347359356125000000000000000:ℝ)],
![(414806507421468517280719252103113515834231667201/2493117587395134269471871225000000000000000:ℝ), (31866837324457754684098846392263889714032007682579/62327939684878356736796780625000000000000000:ℝ), (32632514421499295374055426545625217625996482352759/62327939684878356736796780625000000000000000:ℝ), (2227068825810294266921713568511328253014053270041/12465587936975671347359356125000000000000000:ℝ)]]
theorem admission30_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1132569302752551728723039140019781187336630697447/278850481847513633252878596440064000000000000000000:ℝ) admission30_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission30_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_08_coefficients]
def admission30_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(62201702239400589964652184773012111447/311639698424391783683983903125000:ℝ), (21839575925165216646380310304277350570459/38954962303048972960497987890625000:ℝ), (2545240255710748378620735990635417849048/4869370287881121620062248486328125:ℝ), (31489086091546151805082521559232843264/194774811515244864802489939453125:ℝ)],
![(458540347489002423959839737771854676403/3895496230304897296049798789062500:ℝ), (6241396705750197811687354380124325796959/19477481151524486480248993945312500:ℝ), (1401832154170050583652194420675454485616/4869370287881121620062248486328125:ℝ), (82938297876227796635832898940978901376/973874057576224324012449697265625:ℝ)]]
theorem admission30_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (647955452158029661217444522976397667/170196827299507832795946408960000000000:ℝ) admission30_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission30_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_09_coefficients]
def admission30_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6863266776370191579254057488/1462826028545947265625:ℝ), (3789595182543831827956753856/292565205709189453125:ℝ), (17311665896178910806342866096/1462826028545947265625:ℝ), (5227157691861193245813154304/1462826028545947265625:ℝ)],
![(10391091460585654104096283456/1462826028545947265625:ℝ), (28074789311472372178015182592/1462826028545947265625:ℝ), (24984721382884393042891514816/1462826028545947265625:ℝ), (1460287039524534993794523136/292565205709189453125:ℝ)],
![(382355993048315741203821632/162536225393994140625:ℝ), (2957481347604263226181340416/487608676181982421875:ℝ), (2474704011920840261578286144/487608676181982421875:ℝ), (664360927836524259008410624/487608676181982421875:ℝ)]]
theorem admission30_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (648789968590355721687901/908968453753241600000000000:ℝ) admission30_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission30_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_10_coefficients]
def admission30_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7453519138312321590211871799940/99724703495805370778874849:ℝ), (1609349036503889920978633995520/11080522610645041197652761:ℝ), (7034321946414519399328176455680/99724703495805370778874849:ℝ)],
![(6978227631946425572246601774952/99724703495805370778874849:ℝ), (1505352836778873676822086304256/11080522610645041197652761:ℝ), (6573516108348965834697788895232/99724703495805370778874849:ℝ)]]
theorem admission30_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1604862331139884236986764867/8509841364975391639797320448:ℝ) admission30_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission30_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_11_coefficients]
def admission30_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission30_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission30_12_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission30_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_12_coefficients]
def admission30_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(90888625094643931/20000000000000000000:ℝ)]]
theorem admission30_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (90888625094643931/20000000000000000000:ℝ) admission30_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission30_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_13_coefficients]
def admission30_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission30_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission30_14_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission30_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_14_coefficients]
theorem admission30_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission30_00_pos hδ hp
 · exact admission30_01_pos hδ hp
 · exact admission30_02_pos hδ hp
 · exact admission30_03_pos hδ hp
 · exact admission30_04_pos hδ hp
 · exact admission30_05_pos hδ hp
 · exact admission30_06_pos hδ hp
 · exact admission30_07_pos hδ hp
 · exact admission30_08_pos hδ hp
 · exact admission30_09_pos hδ hp
 · exact admission30_10_pos hδ hp
 · exact admission30_11_pos hδ hp
 · exact admission30_12_pos hδ hp
 · exact admission30_13_pos hδ hp
 · exact admission30_14_pos hδ hp
#print axioms admission30_all
end
end RH20261023Return.C30
