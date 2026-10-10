import WeightedQRH.HighRows.CubeFiniteError
import WeightedQRH.FullWFiniteError
namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]


private lemma transfer_triangle (A P B : ℂ) : ‖A-B‖ ≤ ‖P-A‖+‖P-B‖ := by
  calc
    _ = ‖-(P-A)+(P-B)‖ := by congr 1; ring
    _ ≤ ‖-(P-A)‖+‖P-B‖ := norm_add_le _ _
    _ = _ := by rw [norm_neg]

theorem finite_cube_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0 < b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0 < e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((1587/2000:ℝ)+ζ)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(167/1000:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2 < B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u) < a u+2*e) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e a H-
        WeightedQRH.FullWContour.finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨Cc,hCc,hcube⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ A hτ hb hζ hA
    e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cw,hCw,hfull⟩ := WeightedQRH.FullWContour.finite_fullW_arbitrary_saving (ι:=ι)
    K τ saving b ζ A hτ hb hζ hA e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cc+Cw,add_nonneg hCc hCw,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hc := hcube η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hw := hfull η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have ht := transfer_triangle (finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
      (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e a H)
    (finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z)
    (WeightedQRH.FullWContour.finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
      (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e a H)
  exact ht.trans ((add_le_add hc hw).trans_eq (by ring))

end SevenEighths.WeightedHighRowFamily
end
end OAI
