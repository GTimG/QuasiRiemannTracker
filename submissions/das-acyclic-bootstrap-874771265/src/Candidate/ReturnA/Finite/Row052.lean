/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row052_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12664085459382263739913383142466082199721/373744906889888469796875000000:ℝ),(37804743831277397289108350029340133258137/373744906889888469796875000000:ℝ),(15047051930701439484068786344668476181587/149497962755955387918750000000:ℝ),(24953942257885417504052786962094278791103/747489813779776939593750000000:ℝ)],
![(12457263812879730492165432104248580325011/186872453444944234898437500000:ℝ),(37184960334518145189892271180454995480429/186872453444944234898437500000:ℝ),(1027736946245272924351659514037750013541/5190901484581784302734375000:ℝ),(681712956280165667157060848147365851781/10381802969163568605468750000:ℝ)],
![(12252766454246645371290762489845835309071/373744906889888469796875000000:ℝ),(36572143170023615277760267335171593335397/373744906889888469796875000000:ℝ),(1039611145604078046511124337207972968741/10678425911139670565625000000:ℝ),(12067013045929691221832145181953295879609/373744906889888469796875000000:ℝ)]]
theorem row052_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (12067013045929691221832145181953295879609/182638609309995924009535930368000000000000:ℝ) row052_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row052_coefficients,Fin.sum_univ_succ]
 ring
theorem row052_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row052_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row052_pos
