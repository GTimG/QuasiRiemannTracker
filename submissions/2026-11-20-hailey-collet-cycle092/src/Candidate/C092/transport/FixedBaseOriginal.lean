/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed base change preserves the original physical mark and full
positive energy, rather than merely its numerical quota. -/
import Candidate.C092.transport.FixedBaseCollar
import Candidate.C092.transport.StrongPairPhysical
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair
namespace QRH.Cycle092.FixedBaseCollar
local notation "O"=>HeckeFamily.O
variable {ι:Type} [Fintype ι] [DecidableEq ι]
variable (M:Ideal O) [NeZero M] (Hr:Subgroup (O⧸M)ˣ) (hHr:RayOrthogonality.globalUnits M ≤ Hr)

theorem original_mark (old fixed:Character) (θ:ι→RayQuotient.Characters M Hr) (W:ℝ→ℂ)
    (U:ℝ) (hu:1<U) (w σ v:ι→ℝ) (t:ℝ) :
    originalMark M Hr hHr old fixed θ W (base U) (fun i=>coord U (w i)) σ v t =
      originalMark M Hr hHr old fixed θ W U w σ v t := by
  funext i z
  have h : originalCoefficients M Hr hHr fixed θ W (base U) (fun i=>coord U (w i)) σ v i =
      originalCoefficients M Hr hHr fixed θ W U w σ v i := by
    funext I
    simp only [originalCoefficients,reconstruct hu]
  simp only [originalMark,originalPools,h,reconstruct hu]

theorem original_energy {U V H fee K:ℝ} (hU:1<U) (hH:0≤H) (hK:0≤K)
    (old fixed η₁ η₂:Character) (θ:ι→RayQuotient.Characters M Hr) (W:ℝ→ℂ)
    (w σ v:ι→ℝ) (t:ℝ) (T:Finset ι) (rows:Finset FreeRow)
    (W₁ W₂:ℝ→ℂ) (t₁ t₂ X₁ X₂:ℝ)
    (h:finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂
      (originalMark M Hr hHr old fixed θ W (base U) (fun i=>coord U (w i)) σ v t) ≤
      K*(base U)^(coord U V+fee+(5/6)*max 0 (H-coord U V))) :
    finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂
      (originalMark M Hr hHr old fixed θ W U w σ v t) ≤
      (K*factor^(fee+(5/6)*H))*U^(V+fee+(5/6)*max 0 (H-V)) := by
  rw [original_mark M Hr hHr old fixed θ W U hU w σ v t] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (radial_cost (V:=V) (e:=fee) hU hH) hK).trans_eq (mul_assoc _ _ _).symm)

#print axioms original_mark
#print axioms original_energy
end QRH.Cycle092.FixedBaseCollar
