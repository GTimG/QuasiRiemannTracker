/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact bounded analytic inlet on initial data supplies HeightAnchor's
physical leaf, with all geometry and normalization gates proved internally. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedControl
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedContract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialTruncated
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource Cycle61InitialMass
open QRH.Record1252270103Low QRH.Record1252270103Source.InitialPhysical
open QRH.Record1252270103Source.FirstTruncatedHeights
open QRH.Record1252270103Source.High.CoupledFirst
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
local instance initialTruncatedSubsetDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem fixed_subset_physical_of_truncated (B lam cap cross K mesh ξ ε b δ:ℝ)
    (hB:B≤1)(hlam:1≤lam)(hcap:cap≤1)(hξ:0≤ξ)(hε:0<ε)(hr:0≤49/100-K*b)
    (htruncated:FixedSubsetTruncatedSupplier B lam cap cross K mesh ξ ε b δ) :
    HeightAnchor.FixedSubsetMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ := by
  intro α instα instDec rayM instRay H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀ T
  obtain ⟨ds,S,hS,Csmall,τ,hCsmall,hτ,htrunc⟩:=htruncated α rayM H hH W hW hsW bΦ hbΦ η
    η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀ T
  let N:=Fintype.card T
  let Cs:=initialSlotBound W hW hsW
  have hCs:1≤Cs:=initialSlotBound_ge_one W hW hsW
  obtain ⟨J,Cc,Ctotal,hCc,hCtotal,hphys⟩:=normalized_physical_from_initial_caps (ι:=T)
    (initialRadialBump bΦ (by linarith)) ds N Cs ξ τ ε hCs hξ hτ hε
  refine ⟨J,S,Ctotal*(Csmall+Cc),τ,mul_pos hCtotal (add_pos hCsmall hCc),hτ,?_⟩
  filter_upwards [htrunc,hphys,eventually_initial_caps N B lam cap hB hlam hcap]
    with Z htrunc hphys hcaps
  intro hZ θ w v t height hw hwm hheight hv hheightcap p X₁ X₂ hX₁ hX₂ hadm hcross hbδ hwb
  dsimp only
  intro hlong₁ hlong₂
  let r:ℝ:=49/100-K*b
  let Y₂:=Z^r
  let Y₁:=X₁*X₂/Y₂
  have hY₂:0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hY₁:0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  have hprod:Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  have hy₂:1≤Y₂:=Real.one_le_rpow hZ.le hr
  have hscaps:=hcaps.2 hZ rayM H hH W hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod (le_refl N) hw hadm hy₂ hlong₁ hlong₂
  have hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ) := by
    intro I hI
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hI
    exact hscaps.2.2.2.2 _ (Finset.mem_image.mpr
      ⟨v,by simpa only [Fintype.mem_piFinset] using hv,rfl⟩)
  have hb:=htrunc hZ θ w v t height hw hwm hheight hv hheightcap p X₁ X₂ hX₁ hX₂
    hadm hcross hbδ hwb hlong₁ hlong₂
  have hb':TruncatedBudget (initialRadialBump bΦ (by linarith)) s
      (markedSourceModifier 1 1 1 1 (fun _=>1)) R₀ 1 Z Z ξ 1 (Real.logb Z (volume s))
      τ 0 (1+|t|+height) Csmall (zero_lt_one.trans hZ) ds (fun _=>(p.control S)^2) geometryDCompensator:=by
    simpa only [s,r,Y₁,Y₂,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hb
  have hh:=hphys hZ s R₀ p S (1+|t|+height) Csmall hS (le_refl N) (fun _=>le_rfl)
    (fun _=>show (1:ℝ)≤2 by norm_num) (fun _=>le_rfl)
    (fun i=>Real.one_le_rpow hZ.le (hw i)) (show (0:ℝ)≤9/4 by norm_num) (show (0:ℝ)≤9/4 by norm_num)
    (show (1:ℝ)≤1 from le_rfl) rfl rfl hscaps.1 hscaps.2.1 hscaps.2.2.1 hscaps.2.2.2.1
    hpool (by linarith [abs_nonneg t]) hCsmall.le hb'
  exact hh

end
end QRH.Record1252270103Source.InitialTruncated
#print axioms QRH.Record1252270103Source.InitialTruncated.fixed_subset_physical_of_truncated
