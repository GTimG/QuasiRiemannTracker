/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row186_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8185440187312318079364639368659824907931/1698603309838620574675312500000000:ℝ),(17413429075707763636177811349996712951511/1698603309838620574675312500000000:ℝ),(406706347101844492431011290551956898547/66351691790571116198254394531250:ℝ),(23108686444636441047952156594906874936/33175845895285558099127197265625:ℝ)],
![(24141994448491134049824934712435972915483/2123254137298275718344140625000000:ℝ),(54031104203703608873166933741311091279959/2123254137298275718344140625000000:ℝ),(4499668040574840663847824186307065494/265406767162284464793017578125:ℝ),(95420003027044803685091416088327016016/33175845895285558099127197265625:ℝ)],
![(14737327932031041666600116626461411922207/2123254137298275718344140625000000:ℝ),(34731144765194053170068077773608517182251/2123254137298275718344140625000000:ℝ),(397423286113680229330403605910598283598/33175845895285558099127197265625:ℝ),(85009058961071038886167314941265462152/33175845895285558099127197265625:ℝ)]]
theorem row186_identity (δ p : ℝ) : rowMargin .newTop .P δ p =
 Record12518109.Bernstein.bsum 2 3 (2888585805579555130994019574363359367/63328521394394361163048550400000000000000:ℝ) row186_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row186_coefficients,Fin.sum_univ_succ]
 ring
theorem row186_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .P δ p := by
 rw [row186_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row186_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row186_pos
