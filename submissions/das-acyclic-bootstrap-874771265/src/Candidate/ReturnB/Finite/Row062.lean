/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row062_coefficients : Fin 3 → Fin 4 → ℝ := ![![(145495482285065054926049534737559/106656877374803608359375000:ℝ),(423745418384950478487553319208677/106656877374803608359375000:ℝ),(12460682348849613605745381797869/3232026587115260859375000:ℝ),(14772386890730509522319451650951/11850764152755956484375000:ℝ)],
![(43272984411013319463529608232589/17776146229133934726562500:ℝ),(1269168647841633387301879821917/179557032617514492187500:ℝ),(121545789926593869114014569226299/17776146229133934726562500:ℝ),(870459446434973970400248890869/395025471758531882812500:ℝ)],
![(420324518619353969638567616261/387843190453831303125000:ℝ),(30405631457737526709657565647311/9696079761345782578125000:ℝ),(1085434833907825760760404497111/359114065235028984375000:ℝ),(1045455676638235744649275964579/1077342195705086953125000:ℝ)]]
theorem row062_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1045455676638235744649275964579/16066491309563125432320000000000:ℝ) row062_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row062_coefficients,Fin.sum_univ_succ]
 ring
theorem row062_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row062_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row062_pos
