import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryTail
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyOriginalProfileControl CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
local instance geometryTailChildDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Arbitrary second-tail saving for every first common child, with one
constant and threshold before the original source, allocation and heights. -/
theorem actual_common_child_second_tail {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B ξ saving : ℝ)(hCs : 1≤Cs)(hb : 0≤b)
    (hlo : 0<lo)(hhi : 0≤hi)(hB : 0≤B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(s : Input α),Fintype.card α≤N → (∀i,s.M i≤Cs) → (∀i,s.hi i≤b) →
      ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C R seed : Ideal O)(alloc : actualAllocations s.pools C)(χ : Character)(t : ℝ)
        (Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),0<K →
      volume (child s C R alloc χ t)≤Z^B → Tsec≤Z^B →
      (volume (child s C R alloc χ t))^2/K≤Tsec →
      ‖secondDiscardedEnergy (child s C R alloc χ t).η (child s C R alloc χ t).t
        (original (child s C R alloc χ t) (R*C) seed).columns
        (original (child s C R alloc χ t) (R*C) seed).beta Φ K Tsec Z ξ‖ /
        volume (child s C R alloc χ t)≤
      Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨F,Ct,hCt,hbound⟩ := actual_subset_second_tail (α:=α) b lo hi B ξ saving hb hlo hhi hB hξ
  refine ⟨F,Ct*Cs^(2*N),mul_pos hCt (pow_pos (zero_lt_one.trans_le hCs) _),?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hm hs p hp₁ hp₂ C R seed alloc χ t Φ K Tsec hK hV hT hnom
  have hh := hz.2 (liveIndices alloc.val) (child s C R alloc χ t) (p.profile 0) (p.profile 1)
    hp₁ hp₂ (p.support 0) (p.support 1) (fun i=>hs i.val) (R*C) seed Φ K Tsec hK hV hT hnom
  have hc := plain_control_sq_le (child s C R alloc χ t) p ∅ N Cs hCs
    ((live_card_le alloc.val).trans hn) (fun i=>hm i.val)
  simp only [Finset.insert_empty] at hc
  have hZpos : 0<Z := zero_lt_one.trans hz.1
  apply hh.trans
  calc
    _≤Ct*(Cs^(2*N)*(p.control {(0,0)})^2)*
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
      gcongr
    _=_ := by ring

/-- A coarse polynomial bound for the literal amplified main radius. This
is used only where the discarded-frequency estimate saves arbitrary powers. -/
theorem actual_geometry_main_radius_cap {α : Type*}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(M Z ξ a reserve B : ℝ)
    (hZ : 1<Z)(hK : 0<Z^M)(hB : 0≤B)(hM : 0≤M)
    (hA : Real.logb Z (volume s)≤B)(ha : a≤B)
    (hω : CenteredMomentSectorLocalization.frequencyLoss Z 32 ξ+reserve≤B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)≤Z^(12*B) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
  let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
  let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
  let A := Real.logb Z (volume s)
  have hv (i : Fin 5) : 0≤v i ∧ v i≤B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact ⟨Real.logb_nonneg hZ hh.1,
      (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2⟩
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (CenteredMomentAmplificationChildInput.volume_pos s)).symm
  have he : Real.logb Z (Cycle63Moment.firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=v 4 := by
    change Real.logb Z (Cycle63Moment.firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm
    rw [Cycle63Moment.first_projector_span]
  have hR : Real.logb Z (Ideal.span {CenteredMomentCanonicalFirst.activeConductor l.1.1 l.1.2}).absNorm=v 3 := by rfl
  have hC : Real.logb Z (l.1.1.absNorm:ℝ)=v 0 := by rfl
  have hD : Real.logb Z (l.1.2.absNorm:ℝ)=v 1 := by rfl
  rw [hV,actual_main_radius_power reflected l src.hC src.hD src.sameSupport Z M A a ξ reserve hZ]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hR,he,hC,hD]
  · have hmax : max (v 1-v 0) 0≤B := max_le (by linarith [(hv 1).2,(hv 0).1]) hB
    linarith [(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2]
  · have hmax : max (v 0-v 1) 0≤B := max_le (by linarith [(hv 0).2,(hv 1).1]) hB
    linarith [(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
