/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission39_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(1504458354978329833/786981005458153:ℝ),(1502671373972871680/786981005458153:ℝ)]
]
theorem admission39_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission39_00_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission39_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_00_coefficients]
def admission39_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(1100737099178297344/786981005458153:ℝ),(1099737099178297344/786981005458153:ℝ)]
]
theorem admission39_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission39_01_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission39_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_01_coefficients]
def admission39_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(560010731857724662/786981005458153:ℝ),(559529601098954752/786981005458153:ℝ)]
]
theorem admission39_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission39_02_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission39_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_02_coefficients]
def admission39_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(41161645241414105841995776/7082829049123377:ℝ),(27417741508223761436422144/2360943016374459:ℝ),(41091590533257178467270656/7082829049123377:ℝ)],
  ![(41126517200729916881704960/7082829049123377:ℝ),(27394324117223004594669568/2360943016374459:ℝ),(41056466409939096902303744/7082829049123377:ℝ)]
]
theorem admission39_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (39154497537554833319/77363380760558272512:ℝ) admission39_03_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission39_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_03_coefficients]
def admission39_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(718213162194083416627500/786981005458153:ℝ),(1434410450187297036800000/786981005458153:ℝ),(716197889406662082560000/786981005458153:ℝ)],
  ![(719360691035364013026850/786981005458153:ℝ),(1436703895170497533761536/786981005458153:ℝ),(717343806029712741892096/786981005458153:ℝ)]
]
theorem admission39_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (512264649443623125/6446948396713189376:ℝ) admission39_04_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission39_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_04_coefficients]
def admission39_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(24165760398374242619582623/44714829855576875:ℝ),(1595072141472785849798951558/1475589385234036875:ℝ),(797601506379344976376162499/1475589385234036875:ℝ)],
  ![(24045140089419039407645597/44714829855576875:ℝ),(1587114428372354208774841094/1475589385234036875:ℝ),(72147660276443397150217513/134144489566730625:ℝ)]
]
theorem admission39_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (72135420268257118222936791/1536389855007256650711040000:ℝ) admission39_05_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission39_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_05_coefficients]
def admission39_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(184886184113537437167964893050459099612200960/68746640427663724059495193026399:ℝ),(1661380150722105549501540543741974037514731520/206239921282991172178485579079197:ℝ),(1658786269601879476606890499484436563796951040/206239921282991172178485579079197:ℝ),(1657851864681491682431187799981500976332800/619339102951925441977434171409:ℝ)],
  ![(185158545892259551822396118963530494803402752/68746640427663724059495193026399:ℝ),(1663830099010854438459049682494747372470476800/206239921282991172178485579079197:ℝ),(1661234911038348529644665553660458006871015424/206239921282991172178485579079197:ℝ),(1660301649917711948007379589424330687119360/619339102951925441977434171409:ℝ)]
]
theorem admission39_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1157996150209679046481280447902275/10147251862764346441358281464365056:ℝ) admission39_06_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission39_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_06_coefficients]
def admission39_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(15567913007178619087734890487201470510740/5574051926567328977796907542681:ℝ),(10368002109504552549472112316235798384640/1858017308855776325932302514227:ℝ),(15536101257026233356766473500771043246080/5574051926567328977796907542681:ℝ)],
  ![(15537613580016673472389689057674995730302/5574051926567328977796907542681:ℝ),(10347812833656342949091869001218555172864/1858017308855776325932302514227:ℝ),(15505832848905606427399464460505443205120/5574051926567328977796907542681:ℝ)]
]
theorem admission39_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (7393757271244815076541645269634935/30441755588293039324074844393095168:ℝ) admission39_07_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission39_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_07_coefficients]
def admission39_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(422076036344698500016769069181407035475610170151581110553/7497810033799458959889521380371093750000000000:ℝ),(41985329045015221590258154162661653086464677659535977400871/247427731115382145676354205552246093750000000000:ℝ),(464036165138489156147987285120467398228870259025086075483303/2721705042269203602439896261074707031250000000000:ℝ),(51803715385545619259457388831112219126667597258157359901487/907235014089734534146632087024902343750000000000:ℝ)],
  ![(1097266029556881386421123459896924317492463206858755047333/18744525084498647399723803450927734375000000000:ℝ),(6820349629536639938869714837530273300248983628777871629897/38660582986778460261930344617538452148437500000:ℝ),(2411679411687963935844829768208600818120868245107263098879811/13608525211346018012199481305373535156250000000000:ℝ),(10767086348634549870994418028663897384168535495122060576931/181447002817946906829326417404980468750000000000:ℝ)]
]
theorem admission39_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (422076036344698500016769069181407035475610170151581110553/175870492053718798910639691649224015872000000000000000000000:ℝ) admission39_08_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission39_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_08_coefficients]
def admission39_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2226421460924231017169161487067875812915867145524/10886820169076814409759585044298828125:ℝ),(6662322654335216081470536476890546610623582201808/10886820169076814409759585044298828125:ℝ),(201375322168922158968471056617217938755442081792/329903641487176194235138940736328125:ℝ),(2209484440424510636015332802436542631588084580352/10886820169076814409759585044298828125:ℝ)],
  ![(10997881255888641154777817802144952251074116537382/54434100845384072048797925221494140625:ℝ),(32909229307482594600593965098324363633795051665176/54434100845384072048797925221494140625:ℝ),(994692067668040002358651658536754702635338088448/1649518207435880971175694703681640625:ℝ),(2182698038553146632324520141336833028375548264448/10886820169076814409759585044298828125:ℝ)]
]
theorem admission39_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (520395764959608705598001513799865967840087/60883511176586078648149688786190336000000000:ℝ) admission39_09_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission39_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_09_coefficients]
def admission39_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(10272985763969680695554609956261031936/69168252432845478515625:ℝ),(30723418597956631484124073694984695808/69168252432845478515625:ℝ),(30627899312334729901335844521186295808/69168252432845478515625:ℝ),(10177466487686158019016380782462631936/69168252432845478515625:ℝ)],
  ![(20408482791375467593595436795275988992/69168252432845478515625:ℝ),(61034616631904832859574868119533408256/69168252432845478515625:ℝ),(5531256690008988686269799106803531776/6288022948440498046875:ℝ),(20217689768261209501738358850581430272/69168252432845478515625:ℝ)],
  ![(225230534134251042486053778992278528/1537072276285455078125:ℝ),(3367869924168449127501717128107826176/7685361381427275390625:ℝ),(3357283979876431054933065985651474432/7685361381427275390625:ℝ),(1115566727418495616424117752505040896/7685361381427275390625:ℝ)]
]
theorem admission39_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (598436626599220070112768398079/264067006329372236840960000000000:ℝ) admission39_10_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission39_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_10_coefficients]
def admission39_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(12767524473412631665504291525998889851244/5574051926567328977796907542681:ℝ),(25509025545478546499943252629574440050688/5574051926567328977796907542681:ℝ),(12741508673638084832029049993703633977344/5574051926567328977796907542681:ℝ)],
  ![(12742052790832861556343562217264446181506/5574051926567328977796907542681:ℝ),(25458108771081154728370306967305685553152/5574051926567328977796907542681:ℝ),(12716063573815224206206557164909668335616/5574051926567328977796907542681:ℝ)]
]
theorem admission39_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12126983236136650282103116192731541/60883511176586078648149688786190336:ℝ) admission39_11_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission39_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_11_coefficients]
def admission39_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission39_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission39_12_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission39_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_12_coefficients]
def admission39_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission39_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission39_13_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission39_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_13_coefficients]
def admission39_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission39_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission39_14_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission39_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_14_coefficients]
theorem admission39_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission39_00_pos hδ hp
 · exact admission39_01_pos hδ hp
 · exact admission39_02_pos hδ hp
 · exact admission39_03_pos hδ hp
 · exact admission39_04_pos hδ hp
 · exact admission39_05_pos hδ hp
 · exact admission39_06_pos hδ hp
 · exact admission39_07_pos hδ hp
 · exact admission39_08_pos hδ hp
 · exact admission39_09_pos hδ hp
 · exact admission39_10_pos hδ hp
 · exact admission39_11_pos hδ hp
 · exact admission39_12_pos hδ hp
 · exact admission39_13_pos hδ hp
 · exact admission39_14_pos hδ hp
#print axioms admission39_all
end
end RH20261023Finite
