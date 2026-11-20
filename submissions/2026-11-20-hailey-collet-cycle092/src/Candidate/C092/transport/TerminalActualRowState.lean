/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original regular free rows produce the natural state. No ball filling,
new exceptional exclusions or inferred anchored base is introduced. -/
import Candidate.C092.transport.MediumReplaceSourceUpper
import Candidate.C092.transport.OriginalGlobalResponse
import Candidate.C092.transport.TerminalResponseCeilingRows
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorPlainFiberSource CenteredMomentWholeSlotDeletion
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open ConcreteTraceCRT ConcretePrimeRowBridge HeckeDetectorZeros
open QRH.Cycle092.LowActual QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

theorem fixed_character_conductor (eta : Character) {collar : ℝ} (hc : 0< collar) :
    ∀ᶠ U : ℝ in atTop,1< U ∧ (eta.modulus.absNorm:ℝ)≤ U^collar := by
  filter_upwards [(tendsto_rpow_atTop hc).eventually (eventually_ge_atTop (eta.modulus.absNorm:ℝ)),
    eventually_gt_atTop (1:ℝ)] with U hmod hU
  exact ⟨hU,hmod⟩

/-- State built at the ACTUAL cofactor radius U^V, retaining the original
character, exceptional modulus Q and literal unit puncture. -/
def state (eta : Character) (Q : Ideal O) (bPhi U V collar : ℝ)
    (hU : 1≤ U) (hV : 0≤ V) (hc : 0≤ collar)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bPhi)
    (hmod : (eta.modulus.absNorm:ℝ)≤ U^collar) : NaturalState U 0 bPhi :=
  regularState eta Q radialMajorant bPhi U V collar hU hV hc hPhi radialMajorant_nonneg hmod

theorem state_geometry (eta : Character) (Q : Ideal O) (bPhi U V collar : ℝ)
    (hU : 1≤ U) (hV : 0≤ V) (hc : 0≤ collar)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bPhi)
    (hmod : (eta.modulus.absNorm:ℝ)≤ U^collar) :
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).character=eta ∧
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).fixedModulus=Q ∧
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).puncture=1 ∧
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).mask=fixedBadMask*idealGenerator 1 ∧
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).width=V+collar := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Every original kept free row in its true radius lies on the plateau of
the same radial state. This asserts nothing about rows outside the finite set. -/
theorem state_row_support (eta : Character) (Q : Ideal O) (bPhi U V collar : ℝ)
    (hU : 1≤ U) (hV : 0≤ V) (hc : 0≤ collar)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bPhi)
    (hmod : (eta.modulus.absNorm:ℝ)≤ U^collar)
    (u : FreeRow) (hkeep : initialKeep eta Q u.val) (hrow : rowNorm u≤ U^V) :
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).radial.keep u.val ∧
    (state eta Q bPhi U V collar hU hV hc hPhi hmod).radial.profile
      (‖eisEmbedding u.val‖^2/(state eta Q bPhi U V collar hU hV hc hPhi hmod).radial.scale)=1 := by
  refine ⟨hkeep,?_⟩
  change radialMajorant (‖eisEmbedding u.val‖^2/(U^V))=1
  apply radialMajorant_one
  exact ⟨div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _).le,
    (div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)).mpr (by
      simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,rowNorm,one_mul] using hrow)⟩

/-- The native universal boundary bounds this SAME full union dictionary. -/
theorem family_band_upper (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    {U Bmask bPhi : ℝ} (s : NaturalState U Bmask bPhi) (eta0 : Character)
    (hQM : s.fixedModulus≤ M) (hQeta : s.fixedModulus≤ eta0.modulus)
    (u : FreeRow) (hu : s.radial.keep u.val) (a T : ℝ)
    (hcurrent : a≤ zeroMaximum (family M H hH s eta0 (naturalRow s.character u.val (s.row_ne_zero u.val hu)))
      (family_nonprincipal M H hH s eta0 hQM hQeta hu _) T) : a≤7/8 := by
  have hb:=HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))
  exact hcurrent.trans ((CenteredMomentPrimeGlobal.zeroMaximum_le_beta _ _ T hbeta).trans hb)

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.state_row_support
#print axioms QRH.Cycle092.TerminalActualRow.family_band_upper
