/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row217_coefficients : Fin 3 → Fin 4 → ℝ := ![![(36039413134302938689423449057728593304/75383719931370795964539626953125:ℝ),(86885887285863733099792548462600952712/75383719931370795964539626953125:ℝ),(66426445503945011494856186489917775512/75383719931370795964539626953125:ℝ),(15574391189957273855420894272545416104/75383719931370795964539626953125:ℝ)],
![(396619885204949197916709250376435481488/376918599656853979822698134765625:ℝ),(965235432666354464378406470188499674256/376918599656853979822698134765625:ℝ),(748710527926643114338954799046395965048/376918599656853979822698134765625:ℝ),(36007277751950988794412510940616354456/75383719931370795964539626953125:ℝ)],
![(235808377851146615002714208010064453468/376918599656853979822698134765625:ℝ),(588290331715529736362753214402494846896/376918599656853979822698134765625:ℝ),(473399145774456428999724725045751701813/376918599656853979822698134765625:ℝ),(24177286252938956617891666154883011677/75383719931370795964539626953125:ℝ)]]
theorem row217_identity (δ p : ℝ) : rowMargin .newKink .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1946798898744659231927611784068177013/4496814052167512959960923242496000000000:ℝ) row217_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row217_coefficients,Fin.sum_univ_succ]
 ring
theorem row217_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .P δ p := by
 rw [row217_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row217_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row217_pos
