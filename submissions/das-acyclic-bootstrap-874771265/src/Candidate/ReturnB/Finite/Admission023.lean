/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission023_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21665293107848019968/1474511733:ℝ),(64605214856777302016/1474511733:ℝ),(64214550390010544128/1474511733:ℝ),(21274628641081262080/1474511733:ℝ)],
![(43330586215696039936/1474511733:ℝ),(129210429713554604032/1474511733:ℝ),(128429100780021088256/1474511733:ℝ),(42549257282162524160/1474511733:ℝ)],
![(21665293107848019968/1474511733:ℝ),(64605214856777302016/1474511733:ℝ),(64214550390010544128/1474511733:ℝ),(21274628641081262080/1474511733:ℝ)]]
theorem admission023_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (619173185/655338548:ℝ) admission023_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission023_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_00_coefficients]
def admission023_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15860061742945009664/1474511733:ℝ),(47365436864035028992/1474511733:ℝ),(47150688499235028992/1474511733:ℝ),(1738368153127223296/163834637:ℝ)],
![(31720123485890019328/1474511733:ℝ),(94730873728070057984/1474511733:ℝ),(94301376998470057984/1474511733:ℝ),(3476736306254446592/163834637:ℝ)],
![(15860061742945009664/1474511733:ℝ),(47365436864035028992/1474511733:ℝ),(47150688499235028992/1474511733:ℝ),(1738368153127223296/163834637:ℝ)]]
theorem admission023_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (113834637/163834637:ℝ) admission023_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission023_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_01_coefficients]
def admission023_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(125586212866615257595904/23039245828125:ℝ),(125045031263387917484032/7679748609375:ℝ),(8300256644010705158144/511983240625:ℝ),(123962668056933237260288/23039245828125:ℝ)],
![(251172425733230515191808/23039245828125:ℝ),(250090062526775834968064/7679748609375:ℝ),(16600513288021410316288/511983240625:ℝ),(247925336113866474520576/23039245828125:ℝ)],
![(125586212866615257595904/23039245828125:ℝ),(125045031263387917484032/7679748609375:ℝ),(8300256644010705158144/511983240625:ℝ),(123962668056933237260288/23039245828125:ℝ)]]
theorem admission023_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (115449231170987/327669274000000:ℝ) admission023_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission023_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_02_coefficients]
def admission023_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35192842424158257152/4423535199:ℝ),(104653002615107354624/4423535199:ℝ),(103729896236139937792/4423535199:ℝ),(34269736045190840320/4423535199:ℝ)],
![(69438536856100667392/4423535199:ℝ),(206465808485507399680/4423535199:ℝ),(204620901941912797184/4423535199:ℝ),(67593630312506064896/4423535199:ℝ)],
![(34245694431942410240/4423535199:ℝ),(101812805870400045056/4423535199:ℝ),(100891005705772859392/4423535199:ℝ),(33323894267315224576/4423535199:ℝ)]]
theorem admission023_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (124141180021/251650002432:ℝ) admission023_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission023_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_03_coefficients]
def admission023_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3456316392820881390592/2559916203125:ℝ),(30662564972043569951744/7679748609375:ℝ),(30220313821577532669952/7679748609375:ℝ),(9926698027996606889984/7679748609375:ℝ)],
![(21232914142448684710912/7679748609375:ℝ),(62799341140575759186944/7679748609375:ℝ),(61904052226217683714048/7679748609375:ℝ),(6779208409363536412672/2559916203125:ℝ)],
![(10863964963986040539136/7679748609375:ℝ),(428490348913762523136/102396648125:ℝ),(10561246134880050348032/2559916203125:ℝ),(10410927200094002348032/7679748609375:ℝ)]]
theorem admission023_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (14200255434031401/167766668288000000:ℝ) admission023_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission023_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_04_coefficients]
def admission023_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(206731287638712184832/307189944375:ℝ),(46642759221888550807552/23039245828125:ℝ),(46768032026911884182528/23039245828125:ℝ),(15630119377926747237376/23039245828125:ℝ)],
![(628708299569293341696/511983240625:ℝ),(85166191278778136155136/23039245828125:ℝ),(85450796848705012762624/23039245828125:ℝ),(28576479050545076983808/23039245828125:ℝ)],
![(852468460514319100928/1535949721875:ℝ),(38523432056889585347584/23039245828125:ℝ),(38682764821793128580096/23039245828125:ℝ),(12946359672618329746432/23039245828125:ℝ)]]
theorem admission023_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (2497466192913044241/68717227330764800000:ℝ) admission023_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission023_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_05_coefficients]
def admission023_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(281093841610933757005879744519168/139661179649171079328125:ℝ),(2471638550718664370525815293449216/418983538947513237984375:ℝ),(2413992526646047827473895745912832/418983538947513237984375:ℝ),(17458533268986598541460437467136/9310745309944738621875:ℝ)],
![(574416143970060183324000339375104/139661179649171079328125:ℝ),(5052424916099130936636105809763328/418983538947513237984375:ℝ),(4936233794373941580155025819959296/418983538947513237984375:ℝ),(35712317026641871037576022851584/9310745309944738621875:ℝ)],
![(293322302359126426318120594855936/139661179649171079328125:ℝ),(2580786365380466566110290516314112/418983538947513237984375:ℝ),(2522241267727893752681130074046464/418983538947513237984375:ℝ),(18253783757655272496115585384448/9310745309944738621875:ℝ)]]
theorem admission023_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (24974632171134851276579529/203396334877512796774400000:ℝ) admission023_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission023_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_06_coefficients]
def admission023_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43258013847713758414565855853568/11323879431013871296875:ℝ),(128486183061532380885994951539712/11323879431013871296875:ℝ),(127203209839862669106405061689344/11323879431013871296875:ℝ),(1679001625041761865399038640128/452955177240554851875:ℝ)],
![(83775024259839080704066091193344/11323879431013871296875:ℝ),(248792126024175763541513792623616/11323879431013871296875:ℝ),(246268787547607658823722607050752/11323879431013871296875:ℝ),(16250337156654195197254981124096/2264775886202774259375:ℝ)],
![(40517010412125322289500235339776/11323879431013871296875:ℝ),(120305942962643382655518841083904/11323879431013871296875:ℝ),(119065577707744989717317545361408/11323879431013871296875:ℝ),(7855329031445385870259787923456/2264775886202774259375:ℝ)]]
theorem admission023_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1872856386052462070050189/8245797359899167436800000:ℝ) admission023_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission023_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_07_coefficients]
def admission023_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(864591085286002951123105447676737879/14744634675799311584472656250:ℝ),(8052864765196094443177069886277683011/44233904027397934753417968750:ℝ),(2774919528296684997590034841506191099/14744634675799311584472656250:ℝ),(2865637519053544472757578802399228923/44233904027397934753417968750:ℝ)],
![(1230719615309575032929019412512273238/7372317337899655792236328125:ℝ),(11308430643425346463248233728850691652/22116952013698967376708984375:ℝ),(3847014156250803153898620806140673147/7372317337899655792236328125:ℝ),(3924740754312260423978637038737835003/22116952013698967376708984375:ℝ)],
![(1596848145333147114734933377347808597/14744634675799311584472656250:ℝ),(14563996521654598483319397571423700293/44233904027397934753417968750:ℝ),(983821756840984262041441354155031039/2948926935159862316894531250:ℝ),(4983843989570976375199695275076441083/44233904027397934753417968750:ℝ)]]
theorem admission023_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (864591085286002951123105447676737879/225165239907646598807552000000000000000:ℝ) admission023_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission023_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_08_coefficients]
def admission023_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4372466779726816749814263542430488/35387123221918347802734375:ℝ),(12660542079744884069477929107849664/35387123221918347802734375:ℝ),(1356120174220996768332583015768064/3931902580213149755859375:ℝ),(156681060377027821878231077748736/1415484928876733912109375:ℝ)],
![(6840986879851602145324088117361544/35387123221918347802734375:ℝ),(19674115619957329002461365466353472/35387123221918347802734375:ℝ),(697317749221964352287200393191424/1310634193404383251953125:ℝ),(1198898293098182774752569167970304/7077424644383669560546875:ℝ)],
![(2468520100124785395509824574931056/35387123221918347802734375:ℝ),(7013573540212444932983436358503808/35387123221918347802734375:ℝ),(735833073444896288529018163806208/3931902580213149755859375:ℝ),(415492991213043665361413779226624/7077424644383669560546875:ℝ)]]
theorem admission023_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1584979977466749822087912671/412289867994958371840000000000:ℝ) admission023_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission023_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_09_coefficients]
def admission023_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2364327457785370336613308/71997643212890625:ℝ),(6772356313143368484662908/71997643212890625:ℝ),(6452346620343989677523392/71997643212890625:ℝ),(2044327811587554029473792/71997643212890625:ℝ)],
![(3460249967599617790191664/71997643212890625:ℝ),(9775388162083858399409968/71997643212890625:ℝ),(9171001102673313673394944/71997643212890625:ℝ),(571176698294064612835328/14399528642578125:ℝ)],
![(70874360525062687486096/4799842880859375:ℝ),(968558884517633049564112/23999214404296875:ℝ),(874119578904534932886784/23999214404296875:ℝ),(259936011230965320753152/23999214404296875:ℝ)]]
theorem admission023_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (95191410362902339143/134213334630400000000000:ℝ) admission023_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission023_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_10_coefficients]
def admission023_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35545734947633037881308929590272/11323879431013871296875:ℝ),(35196421661206521437002206063616/3774626477004623765625:ℝ),(11616223386496298468331649368064/1258208825668207921875:ℝ),(276019843539841278282297245696/90591035448110970375:ℝ)],
![(68791672892958908653769507105792/11323879431013871296875:ℝ),(68105146100253930164486445999104/3774626477004623765625:ℝ),(22473895723782631281023989448704/1258208825668207921875:ℝ),(66741296106240799689526074146816/11323879431013871296875:ℝ)],
![(6649187589065174154492115503104/2264775886202774259375:ℝ),(32908724439047408727484239935488/3774626477004623765625:ℝ),(723844822485755520846156005376/83880588377880528125:ℝ),(32238815663760639904238918434816/11323879431013871296875:ℝ)]]
theorem admission023_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (7686332622471008277950029/41228986799495837184000000:ℝ) admission023_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission023_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_11_coefficients]
def admission023_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(55207909188960256/439453125:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/439453125:ℝ)],
![(110415818377920512/439453125:ℝ),(110415818377920512/146484375:ℝ),(110415818377920512/146484375:ℝ),(110415818377920512/439453125:ℝ)],
![(55207909188960256/439453125:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/439453125:ℝ)]]
theorem admission023_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission023_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission023_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_12_coefficients]
def admission023_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19307878491852111872/274658203125:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/274658203125:ℝ)],
![(38615756983704223744/274658203125:ℝ),(38615756983704223744/91552734375:ℝ),(38615756983704223744/91552734375:ℝ),(38615756983704223744/274658203125:ℝ)],
![(19307878491852111872/274658203125:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/274658203125:ℝ)]]
theorem admission023_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (4603356955493/1000000000000000:ℝ) admission023_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission023_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_13_coefficients]
def admission023_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)],
![(137438953472/9:ℝ),(137438953472/3:ℝ),(137438953472/3:ℝ),(137438953472/9:ℝ)],
![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)]]
theorem admission023_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission023_14_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission023_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_14_coefficients]
theorem admission023_all {δ p : ℝ}
 (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .P δ p j := by
 intro j
 fin_cases j
 · exact admission023_00_pos hd hp
 · exact admission023_01_pos hd hp
 · exact admission023_02_pos hd hp
 · exact admission023_03_pos hd hp
 · exact admission023_04_pos hd hp
 · exact admission023_05_pos hd hp
 · exact admission023_06_pos hd hp
 · exact admission023_07_pos hd hp
 · exact admission023_08_pos hd hp
 · exact admission023_09_pos hd hp
 · exact admission023_10_pos hd hp
 · exact admission023_11_pos hd hp
 · exact admission023_12_pos hd hp
 · exact admission023_13_pos hd hp
 · exact admission023_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission023_all
