/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row021_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4313378229041030688474537315652189183/467181133612360587246093750:ℝ),(2562001581710989610510643630109540787/93436226722472117449218750:ℝ),(6340202152025840899560661887634210048/233590566806180293623046875:ℝ),(2091887011021114154644242235811452672/233590566806180293623046875:ℝ)],
![(8470962928645780760018328059984824103/467181133612360587246093750:ℝ),(25153964203085222851975692027711511463/467181133612360587246093750:ℝ),(12448044534009815402104270763611613696/233590566806180293623046875:ℝ),(4106543286570256485169453920373270016/233590566806180293623046875:ℝ)],
![(3326605963482756132800201402731586051/373744906889888469796875000:ℝ),(7054842823294199334195733056938301241/266960647778491764140625000:ℝ),(872693124709886342084097476777092864/33370080972311470517578125:ℝ),(2014992820741917997311550418232127744/233590566806180293623046875:ℝ)]]
theorem row021_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (7871065706023117176998243821219249/55736880282591529543925760000000000:ℝ) row021_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row021_coefficients,Fin.sum_univ_succ]
 ring
theorem row021_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row021_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row021_pos
