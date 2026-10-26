/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission27_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(53093841724721149/1636435164017589:ℝ),(49457406560703560/1636435164017589:ℝ)]
]
theorem admission27_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (6182175820087945/6545740656070356:ℝ) admission27_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission27_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_00_coefficients]
def admission27_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(38365925248562848/1636435164017589:ℝ),(36365925248562848/1636435164017589:ℝ)]
]
theorem admission27_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1136435164017589/1636435164017589:ℝ) admission27_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission27_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_01_coefficients]
def admission27_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(19411230447894484/1636435164017589:ℝ),(18443840136982064/1636435164017589:ℝ)]
]
theorem admission27_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1152740008561379/3272870328035178:ℝ) admission27_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission27_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_02_coefficients]
def admission27_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2919787784140031104/115967846268963:ℝ),(235254378182428825472/4909305492052767:ℝ),(335310085961502526208/14727916476158301:ℝ)],
  ![(352712262205641865504/14727916476158301:ℝ),(223210089486588413792/4909305492052767:ℝ),(317296006254123375872/14727916476158301:ℝ)]
]
theorem admission27_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1239437524430169437/2513564411931016704:ℝ) admission27_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission27_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_03_coefficients]
def admission27_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(54871615393887920/12885316252107:ℝ),(12851376192639777920/1636435164017589:ℝ),(5902028843834260480/1636435164017589:ℝ)],
  ![(585556258074359012/125879628001353:ℝ),(14084147886655192864/1636435164017589:ℝ),(6492231728217686528/1636435164017589:ℝ)]
]
theorem admission27_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (5763700042806895/69821233664750464:ℝ) admission27_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission27_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_04_coefficients]
def admission27_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2306845455925493844407/1022771977510993125:ℝ),(14010233714065849729442/3068315932532979375:ℝ),(544012516125396342017/236024302502536875:ℝ)],
  ![(122347020563266520021/78674767500845625:ℝ),(9817619447105372410172/3068315932532979375:ℝ),(5027674276645801591853/3068315932532979375:ℝ)]
]
theorem admission27_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (122347020563266520021/3437353041956945920000:ℝ) admission27_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission27_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_05_coefficients]
def admission27_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(194976366453460093527838716495859375360/891747375329080046262433957182693:ℝ),(179223665583996598664179745159813328640/297249125109693348754144652394231:ℝ),(492172420000798708167195157423096360960/891747375329080046262433957182693:ℝ),(149459462069042357053934638439515750400/891747375329080046262433957182693:ℝ)],
  ![(210356246133362470168176200321077872448/891747375329080046262433957182693:ℝ),(194102254252162244026906182400268291008/297249125109693348754144652394231:ℝ),(535364144254047386078949451145432390656/891747375329080046262433957182693:ℝ),(163394383616035143085419104265705390080/891747375329080046262433957182693:ℝ)]
]
theorem admission27_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2280570405106237137663797583610775/19023944007020374320265257753230784:ℝ) admission27_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission27_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_06_coefficients]
def admission27_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2397634054224355219137590845725200/189773861529917013462956790207:ℝ),(575838006644555281183930917211803520/24101280414299460709795512356289:ℝ),(271830981058212624895129052402456320/24101280414299460709795512356289:ℝ)],
  ![(269560762204785540967721264782679612/24101280414299460709795512356289:ℝ),(508092262625110698174805046380258912/24101280414299460709795512356289:ℝ),(238992339051180227256791314528334080/24101280414299460709795512356289:ℝ)]
]
theorem admission27_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (933563824418672762721841072376305/4113285190707107961138434108806656:ℝ) admission27_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission27_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_07_coefficients]
def admission27_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(13859843191494962366515514998661601564909885610108159/6437307802964599548556493684906250000000000000000:ℝ),(782409156873608242904480028177194917903613012724748237/83685001438539794131234417903781250000000000000000:ℝ),(9218472381129045766661990391454488074888088100865631007/753165012946858147181109761134031250000000000000000:ℝ),(3795512938613655294380129347638429707636152602725551477/753165012946858147181109761134031250000000000000000:ℝ)],
  ![(10244952438778070567550575185356180115878028014800905153/836850014385397941312344179037812500000000000000000:ℝ),(6400995625532641287891791044044007773788388630689937953/167370002877079588262468835807562500000000000000000:ℝ),(149893315257883477651892400688576342646037986920962752459/3765825064734290735905548805670156250000000000000000:ℝ),(10391617313319355018485889259019848587775505009408644341/753165012946858147181109761134031250000000000000000:ℝ)]
]
theorem admission27_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (13859843191494962366515514998661601564909885610108159/9000008622401877248302898562859008000000000000000000000:ℝ) admission27_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission27_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_08_coefficients]
def admission27_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(636379470038714476866716674102109051612659/31381875539452422799212906713917968750:ℝ),(1736220251543664492461426397641155736724851/31381875539452422799212906713917968750:ℝ),(10436878650568114150942769712468011598176/209212503596349485328086044759453125:ℝ),(232896772860193737442136671277536121057104/15690937769726211399606453356958984375:ℝ)],
  ![(5901323789220217124040044999889382021168799/627637510789048455984258134278359375000:ℝ),(3025293971595374185054415131517552820860051/125527502157809691196851626855671875000:ℝ),(523667466394375777737901117701699793291204/26151562949543685666010755594931640625:ℝ),(83625656178772314726662899021116847333936/15690937769726211399606453356958984375:ℝ)]
]
theorem admission27_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5226603511173269670416431188819802958371/1371095063569035987046144702935552000000000:ℝ) admission27_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission27_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_09_coefficients]
def admission27_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1350751214050856805263635776/5326937382869755859375:ℝ),(98165568440979281422202577856/143827309337483408203125:ℝ),(87018124567333791455550657856/143827309337483408203125:ℝ),(8442540051909214591822081984/47942436445827802734375:ℝ)],
  ![(5840282053981007979447006656/15980812148609267578125:ℝ),(10568987036065741062959000704/11063639179806416015625:ℝ),(117239491857584852455814838592/143827309337483408203125:ℝ),(10805079833186430150790296448/47942436445827802734375:ℝ)],
  ![(1662992889093286866106435304/15980812148609267578125:ℝ),(2399560393603434450734597728/9588487289165560546875:ℝ),(9039418727637466339489309544/47942436445827802734375:ℝ),(677450845425051561378542272/15980812148609267578125:ℝ)]
]
theorem admission27_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (31755508379299291939619169/44685589545440296960000000000:ℝ) admission27_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission27_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_10_coefficients]
def admission27_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1970972840967626890360744726925168/189773861529917013462956790207:ℝ),(473502289073040671488827252685123072/24101280414299460709795512356289:ℝ),(223662026659214698193270431643316736/24101280414299460709795512356289:ℝ)],
  ![(220980105610693753058460357400562084/24101280414299460709795512356289:ℝ),(416653784748839520726794935545106048/24101280414299460709795512356289:ℝ),(196114346312358632218556977089232384/24101280414299460709795512356289:ℝ)]
]
theorem admission27_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (383035832641325453551869095877407/2056642595353553980569217054403328:ℝ) admission27_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission27_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_11_coefficients]
def admission27_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission27_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission27_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission27_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_12_coefficients]
def admission27_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(45103798360955722411/10000000000000000000000:ℝ)]
]
theorem admission27_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (45103798360955722411/10000000000000000000000:ℝ) admission27_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission27_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_13_coefficients]
def admission27_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission27_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission27_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission27_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_14_coefficients]
theorem admission27_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission27_00_pos hδ hp
 · exact admission27_01_pos hδ hp
 · exact admission27_02_pos hδ hp
 · exact admission27_03_pos hδ hp
 · exact admission27_04_pos hδ hp
 · exact admission27_05_pos hδ hp
 · exact admission27_06_pos hδ hp
 · exact admission27_07_pos hδ hp
 · exact admission27_08_pos hδ hp
 · exact admission27_09_pos hδ hp
 · exact admission27_10_pos hδ hp
 · exact admission27_11_pos hδ hp
 · exact admission27_12_pos hδ hp
 · exact admission27_13_pos hδ hp
 · exact admission27_14_pos hδ hp
#print axioms admission27_all
end
end RH20261023Finite
