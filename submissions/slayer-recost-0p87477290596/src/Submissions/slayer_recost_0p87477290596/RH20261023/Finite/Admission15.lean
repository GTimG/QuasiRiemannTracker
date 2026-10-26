/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission15_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(189620902752067113/786981005458153:ℝ),(187833921746608960/786981005458153:ℝ)]
]
theorem admission15_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission15_00_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission15_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_00_coefficients]
def admission15_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(138467137397287168/786981005458153:ℝ),(137467137397287168/786981005458153:ℝ)]
]
theorem admission15_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission15_01_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission15_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_01_coefficients]
def admission15_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(70422330896139254/786981005458153:ℝ),(69941200137369344/786981005458153:ℝ)]
]
theorem admission15_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission15_02_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission15_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_02_coefficients]
def admission15_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(27495447878522969735936/2360943016374459:ℝ),(163873909151204698835200/7082829049123377:ℝ),(81388942515635789627392/7082829049123377:ℝ)],
  ![(27312349137653486779904/2360943016374459:ℝ),(162775789501751225514496/7082829049123377:ℝ),(80840128088790765174784/7082829049123377:ℝ)]
]
theorem admission15_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2467044924584679113/4835211297534892032:ℝ) admission15_03_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission15_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_03_coefficients]
def admission15_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1400626548518117965830/786981005458153:ℝ),(2770281399002267402496/786981005458153:ℝ),(1369728463490241232896/786981005458153:ℝ)],
  ![(1418733444021440574972/786981005458153:ℝ),(2806292760609997793792/786981005458153:ℝ),(1387633410725407784960/786981005458153:ℝ)]
]
theorem admission15_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (125402386183798941/1611737099178297344:ℝ) admission15_04_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission15_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_04_coefficients]
def admission15_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1685658475146042155634472/1475589385234036875:ℝ),(3372183748236757265296036/1475589385234036875:ℝ),(51104816326266454294858/44714829855576875:ℝ)],
  ![(1623110311487759894297974/1475589385234036875:ℝ),(3247491590972591326856884/1475589385234036875:ℝ),(108287634106882441403094/98372625682269125:ℝ)]
]
theorem admission15_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (811555155743879947148987/16504187895585764802560000:ℝ) admission15_05_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission15_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_05_coefficients]
def admission15_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(137214017617010677245468940654210339548160/206239921282991172178485579079197:ℝ),(45177245704665885927610001333622324677632/22915546809221241353165064342133:ℝ),(401573501282639228839516109473349080383488/206239921282991172178485579079197:ℝ),(396973793117829157700364877252127621120/619339102951925441977434171409:ℝ)],
  ![(138827849565628124907656596640632023562240/206239921282991172178485579079197:ℝ),(45712898198939578043483069362929830230016/22915546809221241353165064342133:ℝ),(406373859358545688073678706806285363707904/206239921282991172178485579079197:ℝ),(401758529907321863903864466007654400000/619339102951925441977434171409:ℝ)]
]
theorem admission15_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (283937783087131374621652276934715/2536812965691086610339570366091264:ℝ) admission15_06_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission15_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_06_coefficients]
def admission15_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10609981522124316043861089676854193054/1858017308855776325932302514227:ℝ),(63148321970360685317006704546678719232/5574051926567328977796907542681:ℝ),(31319394513704253303363520830377820160/5574051926567328977796907542681:ℝ)],
  ![(10451038846207513662634748323667066092/1858017308855776325932302514227:ℝ),(62198557803669225973448688973312523776/5574051926567328977796907542681:ℝ),(30846450636819457532004004576227819520/5574051926567328977796907542681:ℝ)]
]
theorem admission15_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (470679483594046898376525948733945/1902609724268314957754677774568448:ℝ) admission15_07_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission15_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_07_coefficients]
def admission15_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(1265384635094767491765675389477393736425477272834177467367/217736403381536288195191700885976562500000000000000:ℝ),(93301808239009204565291518293751243893309813987955640861/4838586741811917515448704464132812500000000000000:ℝ),(4600452965371942572473715978387175961026677501331962774091/217736403381536288195191700885976562500000000000000:ℝ),(1667249573007698637810743287358944609511886527520636402713/217736403381536288195191700885976562500000000000000:ℝ)],
  ![(89426465732156271474255159911324555923589729306536491181/8709456135261451527807668035439062500000000000000:ℝ),(787936655145160724250399358234224651548463337508271611423/24192933709059587577243522320664062500000000000000:ℝ),(1495078313771883894194842117582568071248993821247547129871/43547280676307257639038340177195312500000000000000:ℝ),(2619616615645415870083259527456101388031455379451703426073/217736403381536288195191700885976562500000000000000:ℝ)]
]
theorem admission15_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1265384635094767491765675389477393736425477272834177467367/1246894308896482890714105626341178081280000000000000000000000:ℝ) admission15_08_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission15_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_08_coefficients]
def admission15_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(3417349344873779803538827961360412890189396771/54434100845384072048797925221494140625:ℝ),(915538268708123529441303376755582948638956139/4948554622307642913527084111044921875:ℝ),(3296738607331742518152194041065287012551734016/18144700281794690682932641740498046875:ℝ),(647329118970218920144956472309997823387435008/10886820169076814409759585044298828125:ℝ)],
  ![(3151153416951911603633122113250052421846045758/54434100845384072048797925221494140625:ℝ),(9276960988543293734915634241655018025815444122/54434100845384072048797925221494140625:ℝ),(3033621939283911249817280326511296567149403648/18144700281794690682932641740498046875:ℝ),(595011927815211100436337993599627504612950016/10886820169076814409759585044298828125:ℝ)]
]
theorem admission15_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (36316645984815130641866332617164764685849/3805219448536629915509355549136896000000000:ℝ) admission15_09_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission15_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_09_coefficients]
def admission15_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(80529256929007515759901868053376/13833650486569095703125:ℝ),(394340374918202465654568697111168/23056084144281826171875:ℝ),(386048899706941769011413183955456/23056084144281826171875:ℝ),(377771998916607051370042800799744/69168252432845478515625:ℝ)],
  ![(772889163744408455085154612837888/69168252432845478515625:ℝ),(756429557921869544721628691288576/23056084144281826171875:ℝ),(2219994727908150140892411949217792/69168252432845478515625:ℝ),(80399499947386801312520054243328/7685361381427275390625:ℝ)],
  ![(3737364937217836371281072075264/698669216493388671875:ℝ),(32895162033285024669130977340928/2096007649480166015625:ℝ),(19293179322066431891472095602688/1257604589688099609375:ℝ),(31416707830906362791497194668032/6288022948440498046875:ℝ)]
]
theorem admission15_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (239690458914996054012277181/93773794861282754560000000000:ℝ) admission15_10_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission15_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_10_coefficients]
def admission15_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(26123917531285708888013335117218055718/5574051926567328977796907542681:ℝ),(51828708545697369430268096579212381696/5574051926567328977796907542681:ℝ),(25705767227959541324414417321882943488/5574051926567328977796907542681:ℝ)],
  ![(25723007997355733208265408822554626876/5574051926567328977796907542681:ℝ),(51030227332274159882320195094298053632/5574051926567328977796907542681:ℝ),(25308187543227344045937966871977230336/5574051926567328977796907542681:ℝ)]
]
theorem admission15_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (772344590552592286558165492919227/3805219448536629915509355549136896:ℝ) admission15_11_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission15_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_11_coefficients]
def admission15_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission15_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission15_12_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission15_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_12_coefficients]
def admission15_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission15_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission15_13_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission15_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_13_coefficients]
def admission15_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission15_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission15_14_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission15_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_14_coefficients]
theorem admission15_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission15_00_pos hδ hp
 · exact admission15_01_pos hδ hp
 · exact admission15_02_pos hδ hp
 · exact admission15_03_pos hδ hp
 · exact admission15_04_pos hδ hp
 · exact admission15_05_pos hδ hp
 · exact admission15_06_pos hδ hp
 · exact admission15_07_pos hδ hp
 · exact admission15_08_pos hδ hp
 · exact admission15_09_pos hδ hp
 · exact admission15_10_pos hδ hp
 · exact admission15_11_pos hδ hp
 · exact admission15_12_pos hδ hp
 · exact admission15_13_pos hδ hp
 · exact admission15_14_pos hδ hp
#print axioms admission15_all
end
end RH20261023Finite
