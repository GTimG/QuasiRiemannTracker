import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryNaturalDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseFrequency
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentOriginalCommonHarmonic

/-- The actual geometric parent and retained second row supply both the
coarse frequency cap and the full row-times-missing-radical support cap.
The threshold is chosen before every moving source and row. -/
theorem eventual_geometry_joint_support (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)(b ε : ℝ)(N : ℕ)(hb : 0<b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,∀_hZ : 1<Z,
      ∀{ι α Label : Type}[Fintype ι][DecidableEq ι][Fintype α][DecidableEq α][Fintype Label]
        (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K ξ a reserve M A : ℝ)(hK : 0<K),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^A → K≤Z^M →
      0≤ξ → ξ≤ε → 0≤a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
        (r : secondLiveRows (fun l=>(d l).block))
        (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j),
      (d r.val.1).radius=frequencyRadius
        (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
          (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ →
      let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
      let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
      let l := secondEncodedNonzeroRow (fun k=>(d k).block) first r (!reflected) u₀ unit hf
      normValue (jointSourceRow (!reflected) u₀ unit l.val)≤Z^(M+5*A+ε) ∧
        ((firstSourceMissing (!reflected) l.val.1).absNorm:ℝ)≤Z^A ∧
        ((Ideal.span {jointSourceRow (!reflected) u₀ unit l.val}*
          firstSourceMissing (!reflected) l.val.1).absNorm:ℝ)≤Z^(M+6*A+ε) := by
  filter_upwards [eventual_actual_joint_frequency_coarse u₀ b ε N hb hε] with Z h
  intro hZ ι α Label _ _ _ _ _ reflected s R seed K ξ a reserve M A hK hs hz₁ hz₂ hS hKM
    hξ hξε ha hreserve bin j d first r hfirst hradius unit hf l
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  have he : l.val.1=geometryFirstLabel s R seed K Z ξ hK bin j := hfirst
  have hc : Supported l.val.1.1.1 := by rw [he]; exact src.hC
  have hd : Supported l.val.1.1.2 := by rw [he]; exact src.hD
  have hsupp : CompletedGauss.primeSupport l.val.1.1.1=CompletedGauss.primeSupport l.val.1.1.2 := by
    rw [he]; exact src.sameSupport
  have hCcap : (l.val.1.1.1.absNorm:ℝ)≤Z^A := by
    rw [he]
    exact (actual_geometry_norm_caps s R seed K Z ξ A hs hz₁ hz₂ hS j.1.val 0).2
  have hh := h.2 reflected (!reflected) (firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀)
    l hc hd hsupp K (volume s) a (frequencyLoss Z 32 ξ) reserve ξ M A hK (volume_pos s)
    hξε hKM hCcap ha (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hreserve
  have hret := actual_second_live_retained_weight (fun k=>(d k).block) r.val r.property
  have hn : normValue (jointSourceRow (!reflected) u₀ unit l.val)≤Z^(M+5*A+ε) := by
    apply hh
    change retainedWeight
      (frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N l.val.1) Z ξ)
      (normValue ((d r.val.1).block.frequency*r.val.2.2.2.val))≠0
    rw [he,←hradius]
    exact hret

  have hm := joint_missing_support_cap (!reflected) u₀ unit l hc hd Z (M+5*A+ε) A
    (zero_lt_one.trans hZ) hn hCcap
  refine ⟨hn,hm.1,?_⟩
  convert hm.2 using 1; congr 1; ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
