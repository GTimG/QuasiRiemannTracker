/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row178_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5311677066664729301100348123251479300569133/5446232737137107970271875000000000:ℝ),(6427525655497551146597528465898150403005907/3267739642282264782163125000000000:ℝ),(32484434401585616177110218815286341055998/31911519944162742013311767578125:ℝ),(167623903295296563899300736604430026064/6382303988832548402662353515625:ℝ)],
![(2699875546845216272248767466980067787135471/1361558184284276992567968750000000:ℝ),(469585295650344666204109376450690684127527/116704987224366599362968750000000:ℝ),(67603680093558279041308160067547160590984/31911519944162742013311767578125:ℝ),(495709022278984080725828008621528008928/6382303988832548402662353515625:ℝ)],
![(196585708348642609482356495530556813612371/194508312040610998938281250000000:ℝ),(1687651956349312965279276888612947160133819/816934910570566195540781250000000:ℝ),(35408857234289547478579718436619791232328/31911519944162742013311767578125:ℝ),(347334819074313438566675671534346948912/6382303988832548402662353515625:ℝ)]]
theorem row178_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (10476493955956035243706296037776876629/3118852198987792453378485780480000000000000:ℝ) row178_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row178_coefficients,Fin.sum_univ_succ]
 ring
theorem row178_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row178_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row178_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row178_pos
