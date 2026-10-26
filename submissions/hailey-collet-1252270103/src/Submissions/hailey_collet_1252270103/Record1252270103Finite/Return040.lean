/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1228979595726388681647918333991/4743220650890625000000000:ℝ), (89218603629035422447908377355977/118580516272265625000000000:ℝ), (86304523748346792056761442909303/118580516272265625000000000:ℝ), (27810410012471086650051023903101/118580516272265625000000000:ℝ)],
![(110833667985913849642138834429079/237161032544531250000000000:ℝ), (320657167956534615570069981600511/237161032544531250000000000:ℝ), (77247780627741373479227220989287/59290258136132812500000000:ℝ), (24791905635086181997244434196429/59290258136132812500000000:ℝ)],
![(88622130550038622579304981422517/421619613412500000000000000:ℝ), (51063720453693470541559049702833/84323922682500000000000000:ℝ), (7654464257318641212613214569921/13175612919140625000000000:ℝ), (2445199516117743396097893723307/13175612919140625000000000:ℝ)]]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (2445199516117743396097893723307/24561122652979200000000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row040_coefficients,Fin.sum_univ_succ]
 ring
theorem row040_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row040_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_coefficients]
#print axioms row040_identity
#print axioms row040_pos
end
end Record1252270103Finite
