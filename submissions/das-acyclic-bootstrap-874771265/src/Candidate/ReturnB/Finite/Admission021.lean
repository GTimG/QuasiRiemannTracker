/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission021_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(664061962908336128/45752193:ℝ),(61373802259222102016/1418317983:ℝ),(60989841967968944128/1418317983:ℝ),(20201960558905262080/1418317983:ℝ)],
![(1328123925816672256/45752193:ℝ),(122747604518444204032/1418317983:ℝ),(121979683935937888256/1418317983:ℝ),(40403921117810524160/1418317983:ℝ)],
![(664061962908336128/45752193:ℝ),(61373802259222102016/1418317983:ℝ),(60989841967968944128/1418317983:ℝ),(20201960558905262080/1418317983:ℝ)]]
theorem admission021_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission021_00_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission021_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_00_coefficients]
def admission021_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(483933137974329344/45752193:ℝ),(44791033466812628992/1418317983:ℝ),(44576285102012628992/1418317983:ℝ),(1643019879156023296/157590887:ℝ)],
![(967866275948658688/45752193:ℝ),(89582066933625257984/1418317983:ℝ),(89152570204025257984/1418317983:ℝ),(3286039758312046592/157590887:ℝ)],
![(483933137974329344/45752193:ℝ),(44791033466812628992/1418317983:ℝ),(44576285102012628992/1418317983:ℝ),(1643019879156023296/157590887:ℝ)]]
theorem admission021_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission021_01_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission021_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_01_coefficients]
def admission021_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3843486436761968574464/714878015625:ℝ),(118609758605066865999872/7387072828125:ℝ),(23614287534102541238272/1477414565625:ℝ),(117533116735958546382848/22161218484375:ℝ)],
![(7686972873523937148928/714878015625:ℝ),(237219517210133731999744/7387072828125:ℝ),(47228575068205082476544/1477414565625:ℝ),(235066233471917092765696/22161218484375:ℝ)],
![(3843486436761968574464/714878015625:ℝ),(118609758605066865999872/7387072828125:ℝ),(23614287534102541238272/1477414565625:ℝ),(117533116735958546382848/22161218484375:ℝ)]]
theorem admission021_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission021_02_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission021_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_02_coefficients]
def admission021_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33841648238373896192/4254953949:ℝ),(100624361011414040576/4254953949:ℝ),(99726136603706392576/4254953949:ℝ),(32943423830666248192/4254953949:ℝ)],
![(66781165975578345472/4254953949:ℝ),(198543813444930371584/4254953949:ℝ),(196748906537525706752/4254953949:ℝ),(64986259068173680640/4254953949:ℝ)],
![(32939517737204449280/4254953949:ℝ),(97919452433516331008/4254953949:ℝ),(97022769933819314176/4254953949:ℝ),(32042835237507432448/4254953949:ℝ)]]
theorem admission021_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (238737726491/484119204864:ℝ) admission021_03_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission021_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_03_coefficients]
def admission021_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(639824079330348732416/492471521875:ℝ),(5675005146953206771712/1477414565625:ℝ),(5591987857961512861696/1477414565625:ℝ),(1836454948999352287232/1477414565625:ℝ)],
![(3932842655656852356608/1477414565625:ℝ),(19382699239591991890432/2462357609375:ℝ),(19102515889245024944128/2462357609375:ℝ),(18823663227243360944128/7387072828125:ℝ)],
![(402674083533161231872/295482913125:ℝ),(29773071984009941812736/7387072828125:ℝ),(29347608377927510523904/7387072828125:ℝ),(3213796160748866502656/2462357609375:ℝ)]]
theorem admission021_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656767469286687/8068653414400000:ℝ) admission021_04_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission021_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_04_coefficients]
def admission021_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1066550571492352407296/1477414565625:ℝ),(1922951329823914001152/886448739375:ℝ),(9629989474963254615808/4432243696875:ℝ),(3214884540320741831936/4432243696875:ℝ)],
![(392184869589610860544/295482913125:ℝ),(2852671618469160922112/714878015625:ℝ),(88618286803997807031808/22161218484375:ℝ),(29599331850674632987136/22161218484375:ℝ)],
![(298124592151900631808/492471521875:ℝ),(40359036926946138556672/22161218484375:ℝ),(40468339429181533952768/22161218484375:ℝ),(13524909149070923827456/22161218484375:ℝ)]]
theorem admission021_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (10480942692840256587/264393635083059200000:ℝ) admission021_05_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission021_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_05_coefficients]
def admission021_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16518402932647150375314496884736/8614601658951847996875:ℝ),(435482119858845326909648095645696/77531414930566631971875:ℝ),(425071548966402472603824440737792/77531414930566631971875:ℝ),(9216984476006014818133787803648/5168760995371108798125:ℝ)],
![(168828686395416646169025668686336/43073008294759239984375:ℝ),(4452390994690578530274625492005376/387657074652833159859375:ℝ),(4347458132540481959062897893179392/387657074652833159859375:ℝ),(94301493050038604447300227956736/25843804976855543990625:ℝ)],
![(86236671732180894292453184262656/43073008294759239984375:ℝ),(2274980395396351895726385013776896/387657074652833159859375:ℝ),(2222100387708469596043775689490432/387657074652833159859375:ℝ),(48216570670008530356631288938496/25843804976855543990625:ℝ)]]
theorem admission021_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1098750171185256817118381/9409442238684471838720000:ℝ) admission021_06_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission021_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_06_coefficients]
def admission021_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1609940238344930760861428740096/419088729354414226875:ℝ),(23899622437620408395041117810688/2095443646772071134375:ℝ),(4730225646335150162837667577856/419088729354414226875:ℝ),(7801206985779996223454363779072/2095443646772071134375:ℝ)],
![(78027633726564800812843553043968/10477218233860355671875:ℝ),(231628184986979978994744005146112/10477218233860355671875:ℝ),(229183179496345937440281831276544/10477218233860355671875:ℝ),(3023305129437230370335255166976/419088729354414226875:ℝ)],
![(37779127767941531791307834541568/10477218233860355671875:ℝ),(112130072798877937019538416092672/10477218233860355671875:ℝ),(110927538337967183369340141830144/10477218233860355671875:ℝ),(7315318661406155628221912055808/2095443646772071134375:ℝ)]]
theorem admission021_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (6976431523710399273130333/30517109963300989747200000:ℝ) admission021_07_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission021_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_07_coefficients]
def admission021_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73420004434620659564640410453781352/1364221124200567144775390625:ℝ),(688746101065894737660490914260158696/4092663372601701434326171875:ℝ),(716706187706907288478185338852065624/4092663372601701434326171875:ℝ),(82739103492838802398387639155250328/1364221124200567144775390625:ℝ)],
![(1064869551902215806886221214517506954/6821105621002835723876953125:ℝ),(9827133195710700162224711972029325026/20463316863008507171630859375:ℝ),(10070672027886619017678885260050601584/20463316863008507171630859375:ℝ),(229207949635712685843916863625857328/1364221124200567144775390625:ℝ)],
![(697769529729112509063019162248600194/6821105621002835723876953125:ℝ),(6383402690381226473922257400728531546/20463316863008507171630859375:ℝ),(6487141089352082575287958565790273464/20463316863008507171630859375:ℝ),(1171750769142991067564233795764856/10913768993604537158203125:ℝ)]]
theorem admission021_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (9177500554327582445580051306722669/2604126716868351125094400000000000000:ℝ) admission021_08_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission021_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_08_coefficients]
def admission021_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(969747785738904409834840279327456/6548261396162722294921875:ℝ),(562683079301074768383425764232704/1309652279232544458984375:ℝ),(905987000707230093312752098279424/2182753798720907431640625:ℝ),(874297108503497227721194142302208/6548261396162722294921875:ℝ)],
![(7958754891001749643278895870137628/32741306980813611474609375:ℝ),(22977825776577658314853356880689344/32741306980813611474609375:ℝ),(7360887982291478148909495662108672/10913768993604537158203125:ℝ),(282545227896992964851577726697472/1309652279232544458984375:ℝ)],
![(3110015962307227594104694473500348/32741306980813611474609375:ℝ),(8910748794050789105267712774871744/32741306980813611474609375:ℝ),(2830952978755327682345735170711552/10913768993604537158203125:ℝ),(538429030981467596536694491185152/6548261396162722294921875:ℝ)]]
theorem admission021_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4107887504436245701116138391/762927749082524743680000000000:ℝ) admission021_09_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission021_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_09_coefficients]
def admission021_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(937297264822182327851392/23084602587890625:ℝ),(8097869241946206704102528/69253807763671875:ℝ),(7761001197603536427542528/69253807763671875:ℝ),(825011104207958902331392/23084602587890625:ℝ)],
![(4486440051728346118147232/69253807763671875:ℝ),(4272024773928500619299552/23084602587890625:ℝ),(4058154605015781471951872/23084602587890625:ℝ),(3844849148115188676104192/69253807763671875:ℝ)],
![(328703972151147993169978/13850761552734375:ℝ),(4626140180397209343885154/69253807763671875:ℝ),(4322411400078115925101888/69253807763671875:ℝ),(1339801127038209047066624/69253807763671875:ℝ)]]
theorem admission021_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (654199769061625511263/516393818521600000000000:ℝ) admission021_10_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission021_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_10_coefficients]
def admission021_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33015061017607833198433160630272/10477218233860355671875:ℝ),(32675007374862299510498721083392/3492406077953451890625:ℝ),(32336526180037974249536932544512/3492406077953451890625:ℝ),(31999617433134857415547795013632/10477218233860355671875:ℝ)],
![(63953545142429459780094517463552/10477218233860355671875:ℝ),(63284906264150655940358060535296/3492406077953451890625:ℝ),(62619357599425737695048123482112/3492406077953451890625:ℝ),(495655193186037640353317650432/83817745870882845375:ℝ)],
![(6187696824964325316332271366656/2095443646772071134375:ℝ),(30609898889288356429859339451904/3492406077953451890625:ℝ),(1211313256775510537820447637504/139696243118138075625:ℝ),(29957281715119847628616911290368/10477218233860355671875:ℝ)]]
theorem admission021_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (28569490161056373242012893/152585549816504948736000000:ℝ) admission021_11_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission021_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_11_coefficients]
def admission021_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(55207909188960256/439453125:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/439453125:ℝ)],
![(110415818377920512/439453125:ℝ),(110415818377920512/146484375:ℝ),(110415818377920512/146484375:ℝ),(110415818377920512/439453125:ℝ)],
![(55207909188960256/439453125:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/439453125:ℝ)]]
theorem admission021_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission021_12_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission021_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_12_coefficients]
def admission021_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17484380259611574272/274658203125:ℝ),(17484380259611574272/91552734375:ℝ),(17484380259611574272/91552734375:ℝ),(17484380259611574272/274658203125:ℝ)],
![(34968760519223148544/274658203125:ℝ),(34968760519223148544/91552734375:ℝ),(34968760519223148544/91552734375:ℝ),(34968760519223148544/274658203125:ℝ)],
![(17484380259611574272/274658203125:ℝ),(17484380259611574272/91552734375:ℝ),(17484380259611574272/91552734375:ℝ),(17484380259611574272/274658203125:ℝ)]]
theorem admission021_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission021_13_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission021_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_13_coefficients]
def admission021_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)],
![(137438953472/9:ℝ),(137438953472/3:ℝ),(137438953472/3:ℝ),(137438953472/9:ℝ)],
![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)]]
theorem admission021_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission021_14_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission021_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission021_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission021_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission021_14_coefficients]
theorem admission021_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission021_00_pos hd hp
 · exact admission021_01_pos hd hp
 · exact admission021_02_pos hd hp
 · exact admission021_03_pos hd hp
 · exact admission021_04_pos hd hp
 · exact admission021_05_pos hd hp
 · exact admission021_06_pos hd hp
 · exact admission021_07_pos hd hp
 · exact admission021_08_pos hd hp
 · exact admission021_09_pos hd hp
 · exact admission021_10_pos hd hp
 · exact admission021_11_pos hd hp
 · exact admission021_12_pos hd hp
 · exact admission021_13_pos hd hp
 · exact admission021_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission021_all
