/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def admission36_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(86091951164903/355426639143:ℝ), (767628720731840/3198839752287:ℝ)]]
theorem admission36_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission36_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission36_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_00_coefficients]
def admission36_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(62989219620608/355426639143:ℝ), (562902976585472/3198839752287:ℝ)]]
theorem admission36_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission36_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission36_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_01_coefficients]
def admission36_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31997347187012/355426639143:ℝ), (286047944308352/3198839752287:ℝ)]]
theorem admission36_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission36_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission36_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_02_coefficients]
def admission36_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(36973674928066691840/3198839752287:ℝ), (661086815179226372864/28789557770583:ℝ), (328329392826626146304/28789557770583:ℝ)],
![(4080505676448272896/355426639143:ℝ), (656604359931856859648/28789557770583:ℝ), (326089088139546755072/28789557770583:ℝ)]]
theorem admission36_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9951449223008629/19653671438051328:ℝ) admission36_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission36_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_03_coefficients]
def admission36_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5877289980463397588/3198839752287:ℝ), (11625406744965202688/3198839752287:ℝ), (5748419488820641792/3198839752287:ℝ)],
![(5951339085363295928/3198839752287:ℝ), (3924227398475888128/1066279917429:ℝ), (1940549254187859968/1066279917429:ℝ)]]
theorem admission36_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (350855681690713/4367482541789184:ℝ) admission36_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission36_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_04_coefficients]
def admission36_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6379428807911121128504/5997824535538125:ℝ), (2553986918810840523736/1199564907107625:ℝ), (710025826143918076964/666424948393125:ℝ)],
![(6123856646928707265212/5997824535538125:ℝ), (12260425298120911656872/5997824535538125:ℝ), (409086237283745528444/399854969035875:ℝ)]]
theorem admission36_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1530964161732176816303/33542265920940933120000:ℝ) admission36_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission36_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_05_coefficients]
def admission36_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2346374150776550974503327368019247616/3407447728350247988736212877:ℝ), (6954063272307484411660315748041851392/3407447728350247988736212877:ℝ), (6869422751638131287741008570870071296/3407447728350247988736212877:ℝ), (2261733060477405931618284190847467520/3407447728350247988736212877:ℝ)],
![(2373436237722758947256031035057859584/3407447728350247988736212877:ℝ), (7034907997679467577645816263296969728/3407447728350247988736212877:ℝ), (6949927723462467871841354486172483584/3407447728350247988736212877:ℝ), (2288455390247752087333185257933373440/3407447728350247988736212877:ℝ)]]
theorem admission36_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (269619591293025723888669513565/2326150982553769293643921324032:ℝ) admission36_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission36_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_06_coefficients]
def admission36_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(515800930749797607286376612367860/92093181847303999695573321:ℝ), (113716752602634823494952740571904/10232575760811555521730369:ℝ), (507665763792692289157332725596160/92093181847303999695573321:ℝ)],
![(507832267472732381670163364591480/92093181847303999695573321:ℝ), (111953044982281758365094212686336/10232575760811555521730369:ℝ), (499760933560626146246578409799680/92093181847303999695573321:ℝ)]]
theorem admission36_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (15251493333759342841997632135/62868945474426197125511387136:ℝ) admission36_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission36_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_07_coefficients]
def admission36_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(235341680901681475821018083051601632850918706219237/14389559663641249952433331406250000000000000:ℝ), (145528473205984954544178538824667070721989229694751/2877911932728249990486666281250000000000000:ℝ), (749244408562276911776732994695715327228345217396561/14389559663641249952433331406250000000000000:ℝ), (256943276031698527805453913116081304325474025142043/14389559663641249952433331406250000000000000:ℝ)],
![(299667834480992330160897545374694495040594583906999/14389559663641249952433331406250000000000000:ℝ), (919430669377449029656563475468874314523542719982573/14389559663641249952433331406250000000000000:ℝ), (939847318567135065612841383797679080423326957240657/14389559663641249952433331406250000000000000:ℝ), (320084033418646877217290699943956281712816321165083/14389559663641249952433331406250000000000000:ℝ)]]
theorem admission36_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (235341680901681475821018083051601632850918706219237/82403584212239905096350285346897920000000000000000000:ℝ) admission36_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission36_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_08_coefficients]
def admission36_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(158962117496230725045220442431879000849117/2997824929925260406756944042968750:ℝ), (467905795465943184361860384799424700758533/2997824929925260406756944042968750:ℝ), (229472066766444999034923563414335809077888/1498912464962630203378472021484375:ℝ), (15000053305583711390392445480027943387136/299782492992526040675694404296875:ℝ)],
![(72112500814833666622193749314889194957839/1498912464962630203378472021484375:ℝ), (211974844344343906227489717893446262588231/1498912464962630203378472021484375:ℝ), (207621145792068461997193337798969416869632/1498912464962630203378472021484375:ℝ), (13551768251135983888451657738086454222848/299782492992526040675694404296875:ℝ)]]
theorem admission36_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1654268585343748033258259001231256619/209563151581420657085037957120000000000:ℝ) admission36_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission36_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_09_coefficients]
def admission36_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6868403877906260209219602204032/1405740125516748046875:ℝ), (2237229378605035360011147098752/156193347279638671875:ℝ), (3933124246867704860479178233088/281148025103349609375:ℝ), (78999551248459845944631721984/17354816364404296875:ℝ)],
![(868895619944667561627167624704/93716008367783203125:ℝ), (471234100496730833400809340416/17354816364404296875:ℝ), (4137888046780794340511330003968/156193347279638671875:ℝ), (4034823503382113327847975944192/468580041838916015625:ℝ)],
![(6160040416166865984699992745472/1405740125516748046875:ℝ), (667407784833915889182853963264/52064449093212890625:ℝ), (3512113170552844809553587155968/281148025103349609375:ℝ), (1900199687464495341510290505728/468580041838916015625:ℝ)]]
theorem admission36_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (28994746207649159874119423/13975944133725388800000000000:ℝ) admission36_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission36_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_10_coefficients]
def admission36_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(423334624352690557357454877614348/92093181847303999695573321:ℝ), (93334898928472308270172070018048/10232575760811555521730369:ℝ), (416694737878588194602843582627840/92093181847303999695573321:ℝ)],
![(416641784640218296160127108399752/92093181847303999695573321:ℝ), (91853668028017971087261727270912/10232575760811555521730369:ℝ), (410056370425707138748219079720960/92093181847303999695573321:ℝ)]]
theorem admission36_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6256963660060228557559495235/31434472737213098562755693568:ℝ) admission36_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission36_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_11_coefficients]
def admission36_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission36_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission36_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission36_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_12_coefficients]
def admission36_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission36_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission36_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission36_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_13_coefficients]
def admission36_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission36_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission36_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission36_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_14_coefficients]
theorem admission36_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission36_00_pos hδ hp
 · exact admission36_01_pos hδ hp
 · exact admission36_02_pos hδ hp
 · exact admission36_03_pos hδ hp
 · exact admission36_04_pos hδ hp
 · exact admission36_05_pos hδ hp
 · exact admission36_06_pos hδ hp
 · exact admission36_07_pos hδ hp
 · exact admission36_08_pos hδ hp
 · exact admission36_09_pos hδ hp
 · exact admission36_10_pos hδ hp
 · exact admission36_11_pos hδ hp
 · exact admission36_12_pos hδ hp
 · exact admission36_13_pos hδ hp
 · exact admission36_14_pos hδ hp
#print axioms admission36_all
end
end Record1252270103Return.C30
