/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![![(369124093546773815397200493962177477/237161032544531250000000000:ℝ), (44057828719052707501531277309220461/9486441301781250000000000:ℝ), (730354718577472360627852144262063897/158107355029687500000000000:ℝ), (1793631868823035401484922358640799/1171165592812500000000000:ℝ)],
![(119317945540158237621478059626688781/39526838757421875000000000:ℝ), (71195681190478949559853492459911431/7905367751484375000000000:ℝ), (136576916789731820006408237716117/15249551989746093750000:ℝ), (1303854532297204080875786105414521/439187097304687500000000:ℝ)],
![(347022413135614782539398529336801347/237161032544531250000000000:ℝ), (41405653350837827282887685491297993/9486441301781250000000000:ℝ), (343076289405778540271098028254294721/79053677514843750000000000:ℝ), (2526740352459294231707410939386931/1756748389218750000000000:ℝ)]]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2526740352459294231707410939386931/26827295569760747520000000000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ]
 ring
theorem row044_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
#print axioms row044_identity
#print axioms row044_pos
end
end Record1252270103Finite
