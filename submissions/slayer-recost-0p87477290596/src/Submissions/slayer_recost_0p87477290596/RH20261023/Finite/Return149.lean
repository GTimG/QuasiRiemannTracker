/- Generated 2026-10-23 by exact rational Bernstein conversion.
Candidate c=3130677351/25000000000, h=400051/500000.
Compilation status is recorded separately; no new axioms are introduced.
Original mathematical/formal interface: Hailey Collet and Mark Lewko.
Original source released under Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def row149_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(19199945005625661494328143978218482287/2655273403153539843750000000000:ℝ),(23913482540070843982022384907268660283/1380742169639840718750000000000:ℝ),(2559944058886294590942267409119587923/196686918752114062500000000000:ℝ),(4490329062484764470492185748249397473/1534157966266489687500000000000:ℝ)],
  ![(26188547933436603500798425150503731081/1917697457833112109375000000000:ℝ),(2825637350726681098208586573493375861/88509113438451328125000000000:ℝ),(32591096954364902643799379015861053/1415623123400427246093750000:ℝ),(911647800853816782107927483163369389/191769745783311210937500000000:ℝ)],
  ![(240403906014513318464480037864348104341/34518554240996017968750000000000:ℝ),(22390461804415187408842999869621087679/1380742169639840718750000000000:ℝ),(133601374340704595759419523103908317063/11506184746998672656250000000000:ℝ),(1809921865027720456036969120789908079/767078983133244843750000000000:ℝ)]
]
theorem row149_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1809921865027720456036969120789908079/11714059185799901206282240000000000000000:ℝ) row149_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row149_coefficients,Fin.sum_univ_succ] <;> ring
theorem row149_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row149_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row149_coefficients]
#print axioms row149_identity
#print axioms row149_pos
end
end RH20261023Finite
