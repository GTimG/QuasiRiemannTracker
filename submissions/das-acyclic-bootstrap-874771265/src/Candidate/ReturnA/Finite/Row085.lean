/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row085_coefficients : Fin 3 → Fin 4 → ℝ := ![![(171338999908164890712081504093007587712/4596323892929527208994140625:ℝ),(508869860135454790337922102936659006848/4596323892929527208994140625:ℝ),(14392701261793790635169108431245869056/131323539797986491685546875:ℝ),(23744809067812432264042180428564856832/656617698989932458427734375:ℝ)],
![(48397713691034413326481503870151137248/656617698989932458427734375:ℝ),(1006005233845278677821412527327598401568/4596323892929527208994140625:ℝ),(995702392797210562893871325599756976128/4596323892929527208994140625:ℝ),(328481113598340156597463683425716535296/4596323892929527208994140625:ℝ)],
![(167561067839306060414984453533695682774/4596323892929527208994140625:ℝ),(99496619387501786048195779356404963534/919264778585905441798828125:ℝ),(492305080160484229544915364584252039168/4596323892929527208994140625:ℝ),(162383030331368888898736897597641654272/4596323892929527208994140625:ℝ)]]
theorem row085_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2477768407155897352580824243128077/1096725600108651388631777280000000000:ℝ) row085_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row085_coefficients,Fin.sum_univ_succ]
 ring
theorem row085_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row085_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row085_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row085_pos
