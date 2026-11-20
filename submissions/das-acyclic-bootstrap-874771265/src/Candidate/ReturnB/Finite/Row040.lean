/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![![(49159422846382317521513917/189727952906250000000:ℝ),(3568758048398106723281246099/4743198822656250000000:ℝ),(3452190984253961801817737261/4743198822656250000000:ℝ),(1112418507015413016574339087/4743198822656250000000:ℝ)],
![(403031117432701307187443143/862399785937500000000:ℝ),(12826258303195357212805626757/9486397645312500000000:ℝ),(3089900504301216775294387069/2371599411328125000000:ℝ),(991671501442306066858449023/2371599411328125000000:ℝ)],
![(1181619207585849522790205693/5621568975000000000000:ℝ),(6127589369416091442029198113/10118824155000000000000:ℝ),(918525693539407902968415281/1581066274218750000000:ℝ),(293420256701663793436098427/1581066274218750000000:ℝ)]]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (293420256701663793436098427/2947321154764800000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row040_coefficients,Fin.sum_univ_succ]
 ring
theorem row040_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row040_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row040_pos
