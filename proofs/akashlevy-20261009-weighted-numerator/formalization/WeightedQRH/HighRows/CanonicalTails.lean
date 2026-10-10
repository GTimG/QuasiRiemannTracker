import WeightedQRH.HighRows.PhysicalLargeTail
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalTails
import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalPartition
import WeightedQRH.HighRows.PhysicalSmallTail
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(167/1000:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-681/1000-7221/100000+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(167/1000:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((1587/2000:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((1587/2000:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨C,hC,hmain⟩ := large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((1587/2000:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

end SevenEighths.WeightedHighRowFamily

end

end OAI
