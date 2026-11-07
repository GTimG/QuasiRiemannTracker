/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![![(80269175027315664821811624319/142209169833071477812500000:ℝ),(18367072729059091304934577501/12928106348461043437500000:ℝ),(8406352971983193923839205237/7110458491653573890625000:ℝ),(3847358147396991389838781379/11850764152755956484375000:ℝ)],
![(377863367303863905445432531/493781839698164853515625:ℝ),(2654640266060904168882983/1463057302809377343750:ℝ),(12516891822019538846182754701/8888073114566967363281250:ℝ),(1579901685370744636930709267/4444036557283483681640625:ℝ)],
![(2151673916554690965819914999/8888073114566967363281250:ℝ),(4670650319568977008673438479/8888073114566967363281250:ℝ),(539428492748379905648524631/1481345519094494560546875:ℝ),(31657647993526758853982923/404003323389407607421875:ℝ)]]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (31657647993526758853982923/735465605601339360000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ]
 ring
theorem row035_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row035_pos
