/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row026_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2105236721337234414160738391827/17776146229133934726562500:ℝ),(6005198646045588060243885647731/17776146229133934726562500:ℝ),(11405871101069481934789948286837/35552292458267869453125000:ℝ),(3605815212292659613272091275029/35552292458267869453125000:ℝ)],
![(1678709522853127783325994584929/8888073114566967363281250:ℝ),(4743770527624336155469782526303/8888073114566967363281250:ℝ),(743362170508250302548411362074/1481345519094494560546875:ℝ),(46501093155407480851191424369/296269103818898912109375:ℝ)],
![(1303187665071150034568528956981/17776146229133934726562500:ℝ),(145485450020086689723524675551/711045849165357389062500:ℝ),(3373857064719809184139213451957/17776146229133934726562500:ℝ),(94528491904500832226045501833/1616013293557630429687500:ℝ)]]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (94528491904500832226045501833/753116780135771504640000000000:ℝ) row026_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row026_coefficients,Fin.sum_univ_succ]
 ring
theorem row026_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row026_pos
