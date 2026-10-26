/- Copyright (c) 2026 Sil. Apache-2.0.
Actual original-source admission caps for every genuine live source.
Constants and thresholds precede all allocations, characters and rows.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstExceptionalWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstExceptionalCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstSourceConductorCaps
open CenteredMomentCanonicalFirst CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalAllocations MixedOriginalTail MixedOriginalNormCap
open MixedOriginalTailCaps MixedInnerExceptionalLedger MixedFirstLiveSource
open MixedFirstExceptionalWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem live_product_le (s : Source ι a b) :
    (∏i : liveIndices s.B,(liveSource s).P i)≤∏i,s.P i := by
  change (∏i : liveIndices s.B,s.P i.val)≤_
  rw [Finset.prod_coe_sort (liveIndices s.B) s.P]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.hP i)) (fun i _ _=>s.hP i)

/-- Both full-pool and sharp nonzero-coefficient caps are delivered for
every actual allocation. No nonzero amplitude assumption is necessary
for these coarse admission caps, and the conductor contains R*G. -/
theorem eventually_allocated_caps (N : ℕ)
    (b Lscale Pexp ε Bτ BR BG M : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      ∀cover : OriginalEnclosure s,Fintype.card ι≤N →
      s.X₁≤Z^Lscale → s.X₂≤Z^Lscale → s.Y₁≤Z^Lscale → s.Y₂≤Z^Lscale →
      (∏i,s.P i)≤Z^Pexp → (s.R.absNorm:ℝ)≤Z^BR →
      ∀G : Id,(G.absNorm:ℝ)≤Z^BG → ∀B : actualAllocations (tuplePools s) G,
      poolCap (allocatedLiveSource s hb cover G B)≤Z^(2*Lscale+Pexp+ε) ∧
      sourceNormCap (allocatedLiveSource s hb cover G B).P b
        (allocatedLiveSource s hb cover G B).T (allocatedLiveSource s hb cover G B).d≤
          Z^(2*Lscale+Pexp+ε) ∧
      (∏i,2*(allocatedLiveSource s hb cover G B).P i)≤Z^(Pexp+ε) ∧
      ∀(τ : Character)(radius : ℝ),0≤radius → (τ.modulus.absNorm:ℝ)≤Z^Bτ →
      radius≤Z^M →
      familyConductorBudget (allocatedLiveSource s hb cover G B) τ radius≤
        Z^(Bτ+BR+BG+8*Lscale+4*Pexp+M+5*ε) := by
  have htwo : ∀ᶠZ : ℝ in atTop,(2:ℝ)^N≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) ((2:ℝ)^N)
  filter_upwards [eventually_source_caps N b Lscale Pexp ε hε,
    eventually_family_conductor N b Lscale Pexp ε Bτ (BR+BG) M hb hε,
    htwo] with Z hsource hconductor htwo
  refine ⟨hsource.1,?_⟩
  intro ι instι a s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR G hG B
  have hz := zero_lt_one.trans hsource.1
  have hdim : Fintype.card (liveIndices B.val)≤N :=
    (live_dimension (allocationSource s hb cover G B)).trans hcard
  have hPlive : (∏i,(allocatedLiveSource s hb cover G B).P i)≤Z^Pexp :=
    (live_product_le (allocationSource s hb cover G B)).trans hP
  have hc := hsource.2 (liveIndices B.val) a (allocatedLiveSource s hb cover G B)
    hdim hX₁ hX₂ hY₁ hY₂ hPlive
  have hRlive : ((allocatedLiveSource s hb cover G B).R.absNorm:ℝ)≤Z^(BR+BG) := by
    change ((s.R*G).absNorm:ℝ)≤_
    rw [map_mul,Nat.cast_mul,Real.rpow_add hz]
    exact mul_le_mul hR hG (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
  have hmark : (∏i,2*(allocatedLiveSource s hb cover G B).P i)≤Z^(Pexp+ε) := by
    have hp0 : 0≤∏i,(allocatedLiveSource s hb cover G B).P i :=
      Finset.prod_nonneg (fun i _=>zero_le_one.trans ((allocatedLiveSource s hb cover G B).hP i))
    calc
      _=(2:ℝ)^Fintype.card (liveIndices B.val)*
          (∏i,(allocatedLiveSource s hb cover G B).P i) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
        rfl
      _≤(2:ℝ)^N*Z^Pexp :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hdim) hPlive hp0 (by positivity)
      _≤Z^ε*Z^Pexp := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hz.le _)
      _=Z^(Pexp+ε) := by rw [←Real.rpow_add hz];congr 1;ring
  refine ⟨hc.1,hc.2,hmark,?_⟩
  intro τ radius hr hτ hrad
  have hh := hconductor.2 (liveIndices B.val) a (allocatedLiveSource s hb cover G B)
    hdim hX₁ hX₂ hY₁ hY₂ hPlive hRlive τ radius hr hτ hrad
  convert hh using 1 <;> congr 1 <;> ring

/-- The child character cap also comes from the ACTUAL fixed first
pair. The baseline provides it uniformly for both rays and both sides;
no arbitrary child-conductor premise remains in this specialization.
The coarser quadratic C cap affects only delta admission, not the sharp
first nominal reference or the nonexceptional linear conductor cost. -/
theorem eventually_fixed_pair_family_caps (N : ℕ)
    (b Lscale Pexp ε Bη BR BG M : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      ∀cover : OriginalEnclosure s,Fintype.card ι≤N →
      s.X₁≤Z^Lscale → s.X₂≤Z^Lscale → s.Y₁≤Z^Lscale → s.Y₂≤Z^Lscale →
      (∏i,s.P i)≤Z^Pexp → (s.R.absNorm:ℝ)≤Z^BR →
      ∀(η : Character)(C D : Id)(hC : Supported C),(η.modulus.absNorm:ℝ)≤Z^Bη →
      (C.absNorm:ℝ)≤Z^BG → ∀(E : Finset (CommonIndex C D))(χ ξ : RayCharacter),
      ∀F : FixedPair η C D hC E χ ξ,∀G : Id,(G.absNorm:ℝ)≤Z^BG →
      ∀B : actualAllocations (tuplePools s) G,∀(τ : Character)(radius : ℝ),
      (τ=F.left ∨ τ=F.right) → 0≤radius → radius≤Z^M →
      familyConductorBudget (allocatedLiveSource s hb cover G B) τ radius≤
        Z^(Bη+BR+3*BG+8*Lscale+4*Pexp+M+6*ε) := by
  filter_upwards [eventually_allocated_caps N b Lscale Pexp ε (Bη+2*BG+ε) BR BG M hb hε,
    CenteredMomentFirstSourceConductorCaps.eventually_caps ε hε] with Z halloc hfixed
  refine ⟨halloc.1,?_⟩
  intro ι instι a s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR η C D hC hη hCcap
    E χ ξ F G hG B τ radius hτ hr hrad
  have hc := hfixed.2 η C D hC E χ ξ F Bη BG hη hCcap
  have hτcap : (τ.modulus.absNorm:ℝ)≤Z^(Bη+2*BG+ε) := by
    rcases hτ with rfl|rfl
    · exact hc.1
    · exact hc.2.1
  have hh := (halloc.2 ι a s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR G hG B).2.2.2
    τ radius hr hτcap hrad
  convert hh using 1 <;> congr 1 <;> ring

end
end Candidate.FourthPower.MixedFirstExceptionalCaps
