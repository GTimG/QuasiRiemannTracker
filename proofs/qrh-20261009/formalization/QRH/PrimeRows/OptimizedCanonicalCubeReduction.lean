import QRH.PrimeRows.OptimizedCanonicalReduction
import QRH.PrimeRows.OptimizedCubeFiniteError
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction
import QRH.Geometry
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual cube transport at optimized scales; original row objects unchanged. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.QRHPhysicalTails
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_minus_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (87/100:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=QRH.ell →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^(QRH.h+ζ)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^QRH.lx) (Z^QRH.ly) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^QRH.lx) (Z^QRH.ly) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^(QRH.h+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^QRH.lx) (Z^QRH.ly) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(QRH.C HeckeZeroSupremum.beta+1/200-(QRH.ly/2-(13/75)*QRH.h-1/50)+8*e)+Z^(-saving)) := by
  have hQRH : QRH.h≤9/10 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hlx : 0≤QRH.lx ∧ QRH.lx≤1 := by norm_num [QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hly : 0≤QRH.ly := by norm_num [QRH.ly,QRH.M,QRH.b,QRH.ell,QRH.theta]
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^(QRH.h+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(QRH.h+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(QRH.C HeckeZeroSupremum.beta+1/200-(QRH.ly/2-(13/75)*QRH.h-1/50)+8*e)+Z^(-saving)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤E := by dsimp [E];have : 0≤Z^(QRH.C HeckeZeroSupremum.beta+1/200-(QRH.ly/2-(13/75)*QRH.h-1/50)+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^QRH.lx) (Z^QRH.ly) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^QRH.lx) (Z^QRH.ly) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^QRH.lx) (Z^QRH.ly) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^QRH.lx) (Z^QRH.ly) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

end SevenEighths.QRHPhysicalTails
end
end OAI
