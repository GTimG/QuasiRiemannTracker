/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Completed positive energy of the literal squarefree INITIAL row, centered at
its actual reference pair. The row predicate and radial weight are unchanged. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledInitialMask
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.CompletedEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledInitial
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentHeckeExpansion
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentAddedZeroUniform CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability CenteredMomentAbsoluteEnergy
open QRH.Record1252270103Restoration OAI.SevenEighths.Record1252270103Source
open CoupledFirst
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledInitialEnergyDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def centeredRow (s:Input ι)(R:Ideal O)(A z:O):ℂ :=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    ∑I∈finiteColumns (Fintype.piFinset s.pools),
      coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1 I*
        rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t I

def normalizedCoefficient (s:Input ι)(R:Ideal O)(A:O) :
    supportedColumns (finiteColumns (Fintype.piFinset s.pools))→ℂ :=
  fun I=>(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    (coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1 I*
      rowWeight s.η (fixedBadMask*idealGenerator R) A 1 s.t I)

def centeredRestrictedEnergy (s:Input ι)(R:Ideal O)(A:O)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):ℝ :=
  restrictedEnergy keep Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
    (normalizedCoefficient s R A) Φ K

lemma centeredRow_eq_polynomial (s:Input ι)(R:Ideal O)(A z:O) :
    centeredRow s R A z=rowPolynomial Finset.univ
      (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
      (normalizedCoefficient s R A) z := by
  unfold centeredRow
  have hml:goodLambda∣fixedBadMask*idealGenerator R :=
    (dvd_mul_right goodLambda 2).trans (dvd_mul_right _ _)
  have hm2:(2:O)∣fixedBadMask*idealGenerator R :=
    (dvd_mul_left 2 goodLambda).trans (dvd_mul_right _ _)
  rw [finite_hecke_sum_eq_rowPolynomial s.η (fixedBadMask*idealGenerator R) A z s.t hml hm2
    (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1)]
  simp only [rowPolynomial,normalizedCoefficient,Finset.mul_sum,mul_assoc]

lemma centeredRestrictedEnergy_eq (s:Input ι)(R:Ideal O)(A:O)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ) :
    centeredRestrictedEnergy s R A keep Φ K=
      ∑'z:O,if keep z then ‖centeredRow s R A z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  unfold centeredRestrictedEnergy restrictedEnergy
  simp_rw [centeredRow_eq_polynomial]

lemma centered_energy_summable (s:Input ι)(R:Ideal O)(A:O)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K) :
    Summable (fun z:O=>if keep z then ‖centeredRow s R A z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  simp_rw [centeredRow_eq_polynomial]
  exact restricted_summable keep Finset.univ _ (sourceGenerator_supported _) _ Φ K hK

lemma norm_sq_center_le (x y:ℂ) : ‖x‖^2≤2*(‖x-y‖^2+‖y‖^2) := by
  have h:‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
  have hs:=pow_le_pow_left₀ (norm_nonneg x) h 2
  nlinarith [sq_nonneg (‖x-y‖-‖y‖)]

/-- Exact centering loss on the completed positive norm. No source bound or
bound for an arbitrary modified coefficient is an input. -/
theorem squarefree_initial_energy_centering (s:Input ι)(R:Ideal O)(A:O)
    (b:ℝ)(hb₁:s.b₁≤b)(hb₂:s.b₂≤b)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hΦ:∀x,0≤(Φ x).re) :
    squarefreeEnergy s.η (fixedBadMask*idealGenerator R) A s.t s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.X₁ s.X₂ keep Φ K≤
      2*(centeredRestrictedEnergy s R A keep Φ K+
        squarefreeEnergy s.η (fixedBadMask*idealGenerator R) A s.t s.W₁ s.W₂ b s.slots
          (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.Y₁ s.Y₂ keep Φ K) := by
  let β:=fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)
  let f:=fun z=>squarefreePositiveSlotRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b
    s.slots β s.P s.t s.X₁ s.X₂
  let g:=fun z=>squarefreePositiveSlotRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b
    s.slots β s.P s.t s.Y₁ s.Y₂
  have he (z:O):f z-g z=centeredRow s R A z:=squarefree_initial_row_difference s R A z b hb₁ hb₂
  have hf:=squarefree_energy_summable s.η (fixedBadMask*idealGenerator R) A s.W₁ s.W₂ b
    s.slots β s.P s.t s.X₁ s.X₂ keep Φ K hK
  have hg:=squarefree_energy_summable s.η (fixedBadMask*idealGenerator R) A s.W₁ s.W₂ b
    s.slots β s.P s.t s.Y₁ s.Y₂ keep Φ K hK
  have hc:=centered_energy_summable s R A keep Φ K hK
  have hb:=hf.tsum_le_tsum (g:=fun z=>2*((if keep z then ‖centeredRow s R A z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0)+
      (if keep z then ‖g z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0))) ?_ ((hc.add hg).mul_left 2)
  · rw [tsum_mul_left,hc.tsum_add hg] at hb
    rw [centeredRestrictedEnergy_eq]
    exact hb
  · intro z
    by_cases hz:keep z
    · simp only [hz,ite_true]
      have hh:=mul_le_mul_of_nonneg_right (norm_sq_center_le (f z) (g z)) (hΦ (‖eisEmbedding z‖^2/K))
      rw [he] at hh
      dsimp only [f] at hh
      nlinarith [hh]
    · simp only [hz,ite_false,add_zero,mul_zero,le_refl]

end
end QRH.Record1252270103Source.High.CoupledInitial
#print axioms QRH.Record1252270103Source.High.CoupledInitial.centeredRow_eq_polynomial
#print axioms QRH.Record1252270103Source.High.CoupledInitial.squarefree_initial_energy_centering
