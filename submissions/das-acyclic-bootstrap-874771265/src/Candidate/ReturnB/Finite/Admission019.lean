/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission019_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(89208150422454272/1474511733:ℝ),(261520318974132224/1474511733:ℝ),(255416186680901632/1474511733:ℝ),(83104018129223680/1474511733:ℝ)],
![(178416300844908544/1474511733:ℝ),(523040637948264448/1474511733:ℝ),(510832373361803264/1474511733:ℝ),(166208036258447360/1474511733:ℝ)],
![(89208150422454272/1474511733:ℝ),(261520318974132224/1474511733:ℝ),(255416186680901632/1474511733:ℝ),(83104018129223680/1474511733:ℝ)]]
theorem admission019_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (619173185/655338548:ℝ) admission019_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission019_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_00_coefficients]
def admission019_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64469948583378944/1474511733:ℝ),(190054402550136832/1474511733:ℝ),(186698959350136832/1474511733:ℝ),(6790500598153216/163834637:ℝ)],
![(128939897166757888/1474511733:ℝ),(380108805100273664/1474511733:ℝ),(373397918700273664/1474511733:ℝ),(13581001196306432/163834637:ℝ)],
![(64469948583378944/1474511733:ℝ),(190054402550136832/1474511733:ℝ),(186698959350136832/1474511733:ℝ),(6790500598153216/163834637:ℝ)]]
theorem admission019_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (113834637/163834637:ℝ) admission019_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission019_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_01_coefficients]
def admission019_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(509597059748677025792/23039245828125:ℝ),(501141097198249836544/7679748609375:ℝ),(164228378215940882432/2559916203125:ℝ),(484229172097395458048/23039245828125:ℝ)],
![(1019194119497354051584/23039245828125:ℝ),(1002282194396499673088/7679748609375:ℝ),(328456756431881764864/2559916203125:ℝ),(968458344194790916096/23039245828125:ℝ)],
![(509597059748677025792/23039245828125:ℝ),(501141097198249836544/7679748609375:ℝ),(164228378215940882432/2559916203125:ℝ),(484229172097395458048/23039245828125:ℝ)]]
theorem admission019_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (115449231170987/327669274000000:ℝ) admission019_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission019_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_02_coefficients]
def admission019_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(152115389641785344/4423535199:ℝ),(441644174154924032/4423535199:ℝ),(427089635384492032/4423535199:ℝ),(137560850871353344/4423535199:ℝ)],
![(296806100795785216/4423535199:ℝ),(861042229644623872/4423535199:ℝ),(831968441701892096/4423535199:ℝ),(267732312853053440/4423535199:ℝ)],
![(144690711153999872/4423535199:ℝ),(419398055489699840/4423535199:ℝ),(404878806317400064/4423535199:ℝ),(130171461981700096/4423535199:ℝ)]]
theorem admission019_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (124141180021/251650002432:ℝ) admission019_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission019_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_03_coefficients]
def admission019_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2977662496036752896/511983240625:ℝ),(25407282462457866752/1535949721875:ℝ),(24040375788369412096/1535949721875:ℝ),(7566080814021804032/1535949721875:ℝ)],
![(18690928391327120512/1535949721875:ℝ),(266099205850709487232/7679748609375:ℝ),(252088412441302827008/7679748609375:ℝ),(26481282849076314112/2559916203125:ℝ)],
![(9757940903216861824/1535949721875:ℝ),(46354264512806717824/2559916203125:ℝ),(43962177833151922176/2559916203125:ℝ),(41613444477119922176/7679748609375:ℝ)]]
theorem admission019_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (346347693512961/4194166707200000:ℝ) admission019_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission019_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_04_coefficients]
def admission019_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4732198003502305088/1535949721875:ℝ),(42937709023461393728/4607849165625:ℝ),(43249700672048677696/4607849165625:ℝ),(14508585659094199232/4607849165625:ℝ)],
![(533013136818719232/102396648125:ℝ),(364343232731015615744/23039245828125:ℝ),(368534260840023769216/23039245828125:ℝ),(124118983893219980672/23039245828125:ℝ)],
![(3262999048778483392/1535949721875:ℝ),(149654687613708647104/23039245828125:ℝ),(152285757479780380736/23039245828125:ℝ),(51576055597748984512/23039245828125:ℝ)]]
theorem admission019_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (152953080411491409/4294826708172800000:ℝ) admission019_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission019_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_05_coefficients]
def admission019_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10431027428509788672973639168/1117289437193368634625:ℝ),(2157475710500283601225950304768/83796707789502647596875:ℝ),(1975019550166549721366973349888/83796707789502647596875:ℝ),(13328834394259579346978799616/1862149061988947724375:ℝ)],
![(542121525123667335966319281536/27932235929834215865625:ℝ),(22470261732791678037915631252096/418983538947513237984375:ℝ),(20616746411169956191744752295936/418983538947513237984375:ℝ),(139501238385319808740531339264/9310745309944738621875:ℝ)],
![(281345839410922619141978302336/27932235929834215865625:ℝ),(11682883180290260031785879728256/418983538947513237984375:ℝ),(10741648660337207584909885546496/418983538947513237984375:ℝ),(72857066414021912005637341184/9310745309944738621875:ℝ)]]
theorem admission019_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (610145617413005646376593/5084908371937819919360000:ℝ) admission019_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission019_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_06_coefficients]
def admission019_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(39090883485277635140551192064/2264775886202774259375:ℝ),(113019795156613381074488995328/2264775886202774259375:ℝ),(108830033620446030245385453568/2264775886202774259375:ℝ),(34901121949110284311447650304/2264775886202774259375:ℝ)],
![(73696182237489194829200374144/2264775886202774259375:ℝ),(1064281169773463240363662704512/11323879431013871296875:ℝ),(1023730263476986380553410568192/11323879431013871296875:ℝ),(13117200195638764573429989376/452955177240554851875:ℝ)],
![(6921059750442311937729836416/452955177240554851875:ℝ),(499182193990396334991217727872/11323879431013871296875:ℝ),(479580095374756229326483300352/11323879431013871296875:ℝ),(30684879029083538555702296576/2264775886202774259375:ℝ)]]
theorem admission019_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1872856386052462070050189/8245797359899167436800000:ℝ) admission019_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission019_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_07_coefficients]
def admission019_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(504414789008326898025699417949067/5897853870319724633789062500:ℝ),(6736995970616006494542420033163711/17693561610959173901367187500:ℝ),(2978007507667934747039122063048223/5897853870319724633789062500:ℝ),(3707387358590834030430368422328159/17693561610959173901367187500:ℝ)],
![(35503880708940974245479167615232823/58978538703197246337890625000:ℝ),(70623336269424722851782235240502281/35387123221918347802734375000:ℝ),(32250487632719748290995128276524083/14744634675799311584472656250:ℝ),(7017084968774321377996175410886303/8846780805479586950683593750:ℝ)],
![(30459732818857705265222173435742153/58978538703197246337890625000:ℝ),(57149344328192709862697395174174859/35387123221918347802734375000:ℝ),(49610937727099822846794646237807051/29489269351598623168945312500:ℝ),(10326782578957808725561982399444447/17693561610959173901367187500:ℝ)]]
theorem admission019_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (504414789008326898025699417949067/351820687355697810636800000000000000:ℝ) admission019_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission019_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_08_coefficients]
def admission019_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6139086777787194110321504585488/7077424644383669560546875:ℝ),(16753184534602211257790550820832/7077424644383669560546875:ℝ),(67157532412569257045003327488/31455220641705198046875:ℝ),(4497334424051697474300378899456/7077424644383669560546875:ℝ)],
![(44961521623992264258774915368932/35387123221918347802734375:ℝ),(4814509812086444662379659937528/1415484928876733912109375:ℝ),(11776985839517902549801211869952/3931902580213149755859375:ℝ),(1224070784195529858423680294912/1415484928876733912109375:ℝ)],
![(14266087735056293707167392441492/35387123221918347802734375:ℝ),(7319364525830012054107748866808/7077424644383669560546875:ℝ),(1127431429315581806391931977984/1310634193404383251953125:ℝ),(1623019496925951817818022575104/7077424644383669560546875:ℝ)]]
theorem admission019_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1584979977466749822087912671/412289867994958371840000000000:ℝ) admission019_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission019_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_09_coefficients]
def admission019_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18257140419248157414224/71997643212890625:ℝ),(49140191512791458702672/71997643212890625:ℝ),(43557817879099808912672/71997643212890625:ℝ),(12677157410556507624224/71997643212890625:ℝ)],
![(26308962713971111639448/71997643212890625:ℝ),(68765661823850521637624/71997643212890625:ℝ),(58671018311265559231904/71997643212890625:ℝ),(16219339513886149233728/71997643212890625:ℝ)],
![(2496099408206513828369/23999214404296875:ℝ),(1200269188913557862561/4799842880859375:ℝ),(4519743025544733768628/23999214404296875:ℝ),(1015375043870958284192/23999214404296875:ℝ)]]
theorem admission019_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (95191410362902339143/134213334630400000000000:ℝ) admission019_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission019_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_10_coefficients]
def admission019_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(160710631984218857213657127424/11323879431013871296875:ℝ),(154911913100766587560282299904/3774626477004623765625:ℝ),(49738095787599128240423600128/1258208825668207921875:ℝ),(143617754770311248696622628864/11323879431013871296875:ℝ)],
![(60518316738455823456492205696/2264775886202774259375:ℝ),(291382708858533526091726124416/3774626477004623765625:ℝ),(31152117457044359604269379584/419402941889402640625:ℝ),(2156405027655009986580447232/90591035448110970375:ℝ)],
![(141880951708060260068803901056/11323879431013871296875:ℝ),(136470795757766938531443824512/3774626477004623765625:ℝ),(43718256583533950572384538624/1258208825668207921875:ℝ),(125932873686564999625933275136/11323879431013871296875:ℝ)]]
theorem admission019_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (7686332622471008277950029/41228986799495837184000000:ℝ) admission019_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission019_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_11_coefficients]
def admission019_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(215655895269376/439453125:ℝ),(215655895269376/146484375:ℝ),(215655895269376/146484375:ℝ),(215655895269376/439453125:ℝ)],
![(431311790538752/439453125:ℝ),(431311790538752/146484375:ℝ),(431311790538752/146484375:ℝ),(431311790538752/439453125:ℝ)],
![(215655895269376/439453125:ℝ),(215655895269376/146484375:ℝ),(215655895269376/146484375:ℝ),(215655895269376/439453125:ℝ)]]
theorem admission019_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission019_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission019_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_12_coefficients]
def admission019_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(75421400358797312/274658203125:ℝ),(75421400358797312/91552734375:ℝ),(75421400358797312/91552734375:ℝ),(75421400358797312/274658203125:ℝ)],
![(150842800717594624/274658203125:ℝ),(150842800717594624/91552734375:ℝ),(150842800717594624/91552734375:ℝ),(150842800717594624/274658203125:ℝ)],
![(75421400358797312/274658203125:ℝ),(75421400358797312/91552734375:ℝ),(75421400358797312/91552734375:ℝ),(75421400358797312/274658203125:ℝ)]]
theorem admission019_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (4603356955493/1000000000000000:ℝ) admission019_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission019_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_13_coefficients]
def admission019_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(268435456/9:ℝ),(268435456/3:ℝ),(268435456/3:ℝ),(268435456/9:ℝ)],
![(536870912/9:ℝ),(536870912/3:ℝ),(536870912/3:ℝ),(536870912/9:ℝ)],
![(268435456/9:ℝ),(268435456/3:ℝ),(268435456/3:ℝ),(268435456/9:ℝ)]]
theorem admission019_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission019_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission019_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_14_coefficients]
theorem admission019_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .P δ p j := by
 intro j
 fin_cases j
 · exact admission019_00_pos hd hp
 · exact admission019_01_pos hd hp
 · exact admission019_02_pos hd hp
 · exact admission019_03_pos hd hp
 · exact admission019_04_pos hd hp
 · exact admission019_05_pos hd hp
 · exact admission019_06_pos hd hp
 · exact admission019_07_pos hd hp
 · exact admission019_08_pos hd hp
 · exact admission019_09_pos hd hp
 · exact admission019_10_pos hd hp
 · exact admission019_11_pos hd hp
 · exact admission019_12_pos hd hp
 · exact admission019_13_pos hd hp
 · exact admission019_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission019_all
