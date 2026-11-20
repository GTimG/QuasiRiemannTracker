/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual Q-source weighted first integral. The source, reflected numerator and
prime amplitudes retain the provenance of DirectActualFourth. -/
import Candidate.C092.transport.DirectActualFourth
import Candidate.C092.transport.DirectWeightedIntegral
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter MeasureTheory
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator
namespace QRH.Cycle092.DirectEnergy

/-- The actual original numerator at row-dependent reflected scale. -/
def originalRow {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (G : 𝓢(ℝ,ℂ))
    {rows : Finset FreeRow} (N : rows → ℝ) (Y : ℝ) (i : rows) : ℂ :=
  polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0

/-- Actual canonical prime product with the original row/modulus and source weight. -/
def primeProduct {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {rows : Finset FreeRow}
    {J : Type*} [Fintype J] (U : ℝ) (width : J → ℝ) (z : J → ℂ) (i : rows) : ℂ :=
  ∏ s, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)

/-- Genuine physical first integral from the Q source. The measure space may
contain all three original independent heights. Reflected scales, primitive
presentations and prime heights may vary at every integration point. The
selected product stays squared in the source fourth moment; the full product
has its own amplitude bound. No physical energy or integral bound is assumed. -/
theorem q_original_weighted_first
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (hAffineError : 0 < affineError) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
      (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ)
      (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ),
      0 < loss → 0 < xi → 0 < b → 0 < Cslot →
      ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
        (data : Ω → ∀ i : rows, PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : Ω → rows → ℝ) (Y : Ω → ℝ) (m : ℝ),
      (∀ t, 0 < Y t) → (∀ t i, 0 < N t i ∧ N t i ≤ b*Y t) →
      0 ≤ m → m+xi ≤ 2 →
      (∀ t i, (data t i).combinedConductor ≤
        (fixedConductorConstant F.S : ℝ)*U^m*(Y t/N t i)) →
      ∀ (T : Finset (Fin D.N)) (width : T → ℝ) (z : Ω → T → ℂ) (height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ mesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀ t i, (z t i).re=17/50) → 0 ≤ height →
      (∀ t i, |(z t i).im| ≤ height) →
      (((∑ i, width i) ≤ QRH.Cycle090.physicalCap ∧
        2*(m+xi)+(2+10*QRH.Cycle090.sourceCost)*(∑ i,width i) ≤ 1-QRH.Cycle090.sourceCost) ∨
        (2*(m+xi)+6*κ*(∑ i,width i) ≤ 1 ∨ T=∅)) →
      (∀ t (i : rows), ‖primeProduct F U width (z t) i‖ ≤ Cslot*U^q) →
      ∀ (J : Type) [Fintype J] (fullWidth : J → ℝ) (fullZ : Ω → J → ℂ)
        (K : Ω → ℂ) (L A : ℝ),
      0 < L → 0 ≤ A → Integrable K μ →
      (∀ t (i : rows), L ≤ ‖primeProduct F U width (z t) i‖) →
      (∀ t (i : rows), ‖primeProduct F U fullWidth (fullZ t) i‖ ≤ A) →
      L^2*‖∫ t, K t*(∑ i : rows,
        originalRow F G (N t) (Y t) i * primeProduct F U fullWidth (fullZ t) i) ∂μ‖^4 ≤
        A^4*(rows.card : ℝ)^3*(C*(1+height)^degree*U^(1+D.t+affineError+loss))*
          (∫ t, ‖K t‖ ∂μ)^4 := by
  obtain ⟨mesh,hm,hfourth⟩ := q_original_numerator_fourth hβ affineError hAffineError
  refine ⟨mesh,hm,?_⟩
  intro D F κ hκlo hκhi hκβ G loss xi q b Cslot hloss hxi hb hCslot
  obtain ⟨degree,C,hC,hU⟩ := hfourth D F κ hκlo hκhi hκβ G loss xi q b Cslot
    hloss hxi hb hCslot
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hU] with U hU
  refine ⟨hU.1,?_⟩
  intro rows hrows Ω _ μ data N Y m hY hN hm hmxi hcond T width z height
    hwidth hmesh hcommon hz hheight hzim hgate hslot J _ fullWidth fullZ K L A hL hA hK hselected hfull
  have henergy (t : Ω) :
      (∑ i : rows, ‖originalRow F G (N t) (Y t) i‖^4 *
        ‖primeProduct F U width (z t) i‖^2) ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) :=
    hU.2 rows hrows (data t) (N t) (Y t) m (hY t) (hN t) hm hmxi (hcond t)
      T width (z t) height hwidth hmesh hcommon (hz t) hheight (hzim t) hgate (hslot t)
  have hUpos : 0 < U := lt_trans zero_lt_one hU.1
  have hh := Packet.weighted_first_integral μ (Finset.univ : Finset rows)
    (fun t i => originalRow F G (N t) (Y t) i)
    (fun t i => primeProduct F U width (z t) i)
    (fun t i => primeProduct F U fullWidth (fullZ t) i) K L A
    (C*(1+height)^degree*U^(1+D.t+affineError+loss)) hL hA
    (by positivity) hK (fun t i _ => hselected t i) (fun t i _ => hfull t i)
    (fun t => by simpa using henergy t)
  simpa only [Finset.sum_attach, Finset.sum_filter, Finset.mem_univ, ite_true,
    Finset.card_univ, Fintype.card_coe] using hh
theorem q_original_amplitude_first
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (hAffineError : 0 < affineError) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
      (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ)
      (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ),
      0 < loss → 0 < xi → 0 < b → 0 < Cslot →
      ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
        (data : Ω → ∀ i : rows, PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : Ω → rows → ℝ) (Y : Ω → ℝ) (m : ℝ),
      (∀ t, 0 < Y t) → (∀ t i, 0 < N t i ∧ N t i ≤ b*Y t) →
      0 ≤ m → m+xi ≤ 2 →
      (∀ t i, (data t i).combinedConductor ≤
        (fixedConductorConstant F.S : ℝ)*U^m*(Y t/N t i)) →
      ∀ (T : Finset (Fin D.N)) (width : T → ℝ) (z : Ω → T → ℂ) (height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ mesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀ t i, (z t i).re=17/50) → 0 ≤ height →
      (∀ t i, |(z t i).im| ≤ height) →
      (((∑ i, width i) ≤ QRH.Cycle090.physicalCap ∧
        2*(m+xi)+(2+10*QRH.Cycle090.sourceCost)*(∑ i,width i) ≤ 1-QRH.Cycle090.sourceCost) ∨
        (2*(m+xi)+6*κ*(∑ i,width i) ≤ 1 ∨ T=∅)) →
      (∀ t (i : rows), ‖primeProduct F U width (z t) i‖ ≤ Cslot*U^q) →
      ∀ (J : Type) [Fintype J] (fullWidth : J → ℝ) (fullZ : Ω → J → ℂ)
        (K : Ω → ℂ) (R total selected Ccount : ℝ),
      1 ≤ Ccount → (rows.card : ℝ) ≤ Ccount*U^R → Integrable K μ →
      (∀ t (i : rows), U^selected ≤ ‖primeProduct F U width (z t) i‖) →
      (∀ t (i : rows), ‖primeProduct F U fullWidth (fullZ t) i‖ ≤ U^total) →
      ‖∫ t, K t*(∑ i : rows,
        originalRow F G (N t) (Y t) i * primeProduct F U fullWidth (fullZ t) i) ∂μ‖ ≤
        Ccount*(max 1 C*(1+height)^degree)*
          U^(total-selected/2+(3*R+1+(D.t+affineError+loss))/4)*
          (∫ t, ‖K t‖ ∂μ) := by
  obtain ⟨mesh,hm,hfourth⟩ := q_original_numerator_fourth hβ affineError hAffineError
  refine ⟨mesh,hm,?_⟩
  intro D F κ hκlo hκhi hκβ G loss xi q b Cslot hloss hxi hb hCslot
  obtain ⟨degree,C,hC,hU⟩ := hfourth D F κ hκlo hκhi hκβ G loss xi q b Cslot
    hloss hxi hb hCslot
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hU] with U hU
  refine ⟨hU.1,?_⟩
  intro rows hrows Ω _ μ data N Y m hY hN hm hmxi hcond T width z height
    hwidth hmesh hcommon hz hheight hzim hgate hslot J _ fullWidth fullZ K R total selected Ccount
    hcount hcard hK hselected hfull
  have hUpos : 0 < U := lt_trans zero_lt_one hU.1
  let CM := max 1 C*(1+height)^degree
  have hCM : 1 ≤ CM := by
    have hp : (1:ℝ) ≤ (1+height)^degree := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (le_max_left 1 C) hp
  have henergy (t : Ω) :
      (∑ i : rows, ‖originalRow F G (N t) (Y t) i‖^4 *
        ‖primeProduct F U width (z t) i‖^2) ≤ CM*U^(1+(D.t+affineError+loss)) := by
    have hh := hU.2 rows hrows (data t) (N t) (Y t) m (hY t) (hN t) hm hmxi (hcond t)
      T width (z t) height hwidth hmesh hcommon (hz t) hheight (hzim t) hgate (hslot t)
    have hcc : C*(1+height)^degree ≤ CM :=
      mul_le_mul_of_nonneg_right (le_max_right 1 C) (by positivity)
    have he : 1+D.t+affineError+loss=1+(D.t+affineError+loss) := by ring
    exact hh.trans (by rw [he]; exact mul_le_mul_of_nonneg_right hcc (by positivity))
  let B := Ccount*CM*U^(total-selected/2+(3*R+1+(D.t+affineError+loss))/4)
  have hp (t : Ω) : ‖∑ i : rows,
      originalRow F G (N t) (Y t) i*primeProduct F U fullWidth (fullZ t) i‖ ≤ B := by
    have hh := Packet.weighted_amplitude_bin (Finset.univ : Finset rows)
      (fun i => originalRow F G (N t) (Y t) i)
      (fun i => primeProduct F U width (z t) i)
      (fun i => primeProduct F U fullWidth (fullZ t) i)
      U R total selected (D.t+affineError+loss) Ccount CM hUpos hcount hCM
      (by simpa using hcard) (fun i _ => hselected t i) (fun i _ => hfull t i)
      (by simpa using henergy t)
    exact (norm_sum_le _ _).trans (by simpa using hh)
  have hi := norm_integral_le_of_norm_le
    (f := fun t => K t*(∑ i : rows,
      originalRow F G (N t) (Y t) i*primeProduct F U fullWidth (fullZ t) i))
    (hK.norm.mul_const B) (Filter.Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hp t) (norm_nonneg _))
  simpa only [integral_mul_const, mul_comm (∫ t, ‖K t‖ ∂μ) B] using hi
end QRH.Cycle092.DirectEnergy
#print axioms QRH.Cycle092.DirectEnergy.q_original_weighted_first

#print axioms QRH.Cycle092.DirectEnergy.q_original_amplitude_first
