/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7363181862673526726655279661/23701528305511912968750000:ℝ),(59474993438579254151518190911/71104584916535738906250000:ℝ),(35448385493039858132746374107/47403056611023825937500000:ℝ),(6310626896076764351776883693/28441833966614295562500000:ℝ)],
![(4495653438760585665609003829/11850764152755956484375000:ℝ),(34141511052915709445909769199/35552292458267869453125000:ℝ),(2592745887580452139881473467/3232026587115260859375000:ℝ),(313781109165304655734538017/1422091698330714778125000:ℝ)],
![(2386573920624025819562727997/23701528305511912968750000:ℝ),(16382496371650019164975875637/71104584916535738906250000:ℝ),(12113169377427030759395230951/71104584916535738906250000:ℝ),(189876144827485310707169287/4740305661102382593750000:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (189876144827485310707169287/2157365776430595456000000000:ℝ) row002_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ]
 ring
theorem row002_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row002_pos
