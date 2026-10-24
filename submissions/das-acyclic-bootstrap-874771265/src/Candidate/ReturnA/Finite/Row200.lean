/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row200_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2194731871504954161585806504337130262/5173168820834093026997548828125:ℝ),(5196806624866091205528324663272576414/5173168820834093026997548828125:ℝ),(3857672565728436674745687871391817967/5173168820834093026997548828125:ℝ),(171069201507556763518311552358461863/1034633764166818605399509765625:ℝ)],
![(4428332301741168742026707071388808292/5173168820834093026997548828125:ℝ),(10344297796658619068108758287577225804/5173168820834093026997548828125:ℝ),(7504642624952263902618767354684225732/5173168820834093026997548828125:ℝ),(317629402920850793955085564261661644/1034633764166818605399509765625:ℝ)],
![(505281258600336309191484681245641306/1034633764166818605399509765625:ℝ),(1203368753282530045808273223793248718/1034633764166818605399509765625:ℝ),(901472525114076348399066439562223518/1034633764166818605399509765625:ℝ),(203329228807613179491615968889616106/1034633764166818605399509765625:ℝ)]]
theorem row200_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (79407350730212698488771391065415411/246873232246325699919734636544000000000:ℝ) row200_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row200_coefficients,Fin.sum_univ_succ]
 ring
theorem row200_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row200_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row200_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row200_pos
