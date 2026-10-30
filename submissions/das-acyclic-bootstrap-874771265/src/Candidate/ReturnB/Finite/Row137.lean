/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row137_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7159797642455540995706242605451378/191135956878830684794921875:ℝ),(20496464632919180365306738967829886/191135956878830684794921875:ℝ),(19529967421253859892633823753324288/191135956878830684794921875:ℝ),(1238648176663853917491668189126656/38227191375766136958984375:ℝ)],
![(14176195512264729600964200647611688/191135956878830684794921875:ℝ),(8103812848066016951147834058700984/38227191375766136958984375:ℝ),(38543144353209840664186504609893376/191135956878830684794921875:ℝ),(12200153625447903104818879807750144/191135956878830684794921875:ℝ)],
![(1418779587054714352178570183240552/38227191375766136958984375:ℝ),(20253810930484377483885383295052984/191135956878830684794921875:ℝ),(19243107661847898919157171070860288/191135956878830684794921875:ℝ),(6083132178987624159665961660760064/191135956878830684794921875:ℝ)]]
theorem row137_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (371284923033912607401486917771/178151624106823790346240000000000:ℝ) row137_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row137_coefficients,Fin.sum_univ_succ]
 ring
theorem row137_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row137_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row137_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row137_pos
