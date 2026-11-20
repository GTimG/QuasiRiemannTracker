/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual finite conductor bank supplies every state/row guard of the closed
inverse members. The state uses the true radial V and the proofs the same d. -/
import Candidate.C092.transport.SourceInverseP6CloseUnmarkedEnergy
import Candidate.C092.transport.SourceInverseP6ClosePrice

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.LowActual QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6CloseConductor_493932c1b1008abc_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hHr : RayOrthogonality.globalUnits M  ≤  Hr)

/-- All physical regular rows and every label of their true source union
are admitted at the same finite enlarged conductor, with the margin delta.
No live conductor bound or natural-state field is an assumption. -/
theorem actual_regular_conductor_bank (η η₀ : Character) (Q : Ideal O)
    {lo hi δ : ℝ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hδ : 0 < δ) :
    ∃ bank : Finset ℝ,(∀ d∈bank,lo+2*δ ≤ d ∧ d ≤ hi+3*δ) ∧
    ∃ bΦ : ℝ,2 ≤ bΦ ∧ ∃ hs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ,
    ∀ᶠ Z : ℝ in atTop,∃ hZ : 1 < Z,∃ hη : (η.modulus.absNorm:ℝ) ≤ Z^δ,
    ∀ (V : ℝ) (hVlo : lo ≤ V) (_hVhi : V ≤ hi), ∃ d∈bank,V+2*δ ≤ d ∧ d ≤ V+3*δ ∧
      let st := regularState η Q radialMajorant bΦ Z V δ hZ.le (hlo.trans hVlo) hδ.le hs radialMajorant_nonneg hη;
      st.width ≤ d-δ ∧ st.character=η ∧ st.puncture=1 ∧ st.fixedModulus=Q ∧
      d-δ+0+δ ≤ d ∧
      ∀ u : FreeRow,rowNorm u ≤ Z^V →
        st.radial.profile (‖eisEmbedding u.val‖^2/st.radial.scale)≠0 ∧ rowNorm u ≤ Z^d ∧
        ∀ (F : NaturalRow st.character u.val) j,((family M Hr hHr st η₀ F j).modulus.absNorm:ℝ) ≤ Z^d := by
  obtain ⟨bank,hbank,bΦ,hbΦ,hs,hcond⟩ := source_core_conductors M Hr hHr η η₀ Q lo hi δ hlo hlh hδ
  refine ⟨bank,hbank,bΦ,hbΦ,hs,?_⟩
  filter_upwards [hcond] with Z hZcond
  obtain ⟨hZ,hη,hselect⟩ := hZcond
  refine ⟨hZ,hη,?_⟩
  intro V hVl hVh
  obtain ⟨d,hd,hVd,hdV,hconduct⟩ := hselect V hVl hVh
  refine ⟨d,hd,hVd,hdV,?_⟩
  let st := regularState η Q radialMajorant bΦ Z V δ hZ.le (hlo.trans hVl) hδ.le hs radialMajorant_nonneg hη
  change st.width ≤ d-δ ∧ _
  refine ⟨by rw [show st.width=V+δ from regularState_width ..];linarith,rfl,rfl,rfl,by linarith,?_⟩
  intro u hu
  have hZp := zero_lt_one.trans hZ
  have hscale : 0 < Z^V := Real.rpow_pos_of_pos hZp _
  refine ⟨?_,hu.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)),?_⟩
  · change radialMajorant (‖eisEmbedding u.val‖^2/Z^V)≠0
    rw [radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hscale.le,(div_le_one hscale).mpr ?_⟩]
    · exact one_ne_zero
    · rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span];exact hu
  · exact hconduct u (hlo.trans hVl) hu

#print axioms actual_regular_conductor_bank
end
end QRH.Cycle092.SourceInverseP6
