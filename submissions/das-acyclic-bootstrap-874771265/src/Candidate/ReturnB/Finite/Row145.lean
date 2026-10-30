/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row145_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1951015876165281493708874527/345588687421875000000000:ℝ),(68973940390236418330603029559/5183830311328125000000000:ℝ),(52404698674856531325395471321/5183830311328125000000000:ℝ),(12695996427099335400425559667/5183830311328125000000000:ℝ)],
![(31066985279941491924779196851/3455886874218750000000000:ℝ),(193700282485635047274741713137/10367660622656250000000000:ℝ),(29410595566634960674247438489/2591915155664062500000000:ℝ),(4285763905182317799146407843/2591915155664062500000000:ℝ)],
![(247445583096289618512720471097/55294189987500000000000000:ℝ),(287386873386956385262623662959/33176513992500000000000000:ℝ),(22901101676080290259281286193/5183830311328125000000000:ℝ),(1194926124645506797563883021/5183830311328125000000000:ℝ)]]
theorem row145_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1194926124645506797563883021/9663360093388800000000000000000:ℝ) row145_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row145_coefficients,Fin.sum_univ_succ]
 ring
theorem row145_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row145_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row145_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row145_pos
