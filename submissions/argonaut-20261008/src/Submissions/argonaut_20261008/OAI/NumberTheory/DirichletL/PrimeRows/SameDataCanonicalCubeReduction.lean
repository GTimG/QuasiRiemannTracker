import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.TotalECanonicalReduction
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.SameDataFiniteCubeSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeMellinBoundary CompletedGauss
open HeckeInverseAmplification hiding PrimeIdeal
open SevenEighths.Parameters SevenEighths.PerturbedCentral
open SevenEighths.PerturbedCanonicalLocalPrep
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem canonical_probe_minus_cube_same_D {Delta : ℝ} (D : HighDataPerturbed Delta) (e δ a b B saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : boundary<HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin D.N→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(D.ell j)) →
      ∀W : Fin D.N→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^(physicalHeight+D.t)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(D.ell i)) (Z^sourceLx) (Z^sourceLy) Z-
        principalPhysicalPool η S T W (fun i=>Z^(D.ell i)) W0 W1 (Z^sourceLx) (Z^sourceLy) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^(physicalHeight+D.t))) T hT W (fun i=>Z^(D.ell i))
          W0 W1 (Z^sourceLx) (Z^sourceLy) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+51*rho0/100)+Z^(-saving)) := by
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central_same_D_totalE D D.N e δ a b B saving he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving_same_D (ι:=ι) D τ saving b B hτ hb hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis D.ell (fun j=>(D.slots_bounds j).1.le)
    (SevenEighths.PerturbedSameDataCentral.same_D_totalE D) W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^(physicalHeight+D.t))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(physicalHeight+D.t) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+51*rho0/100)+Z^(-saving)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤E := by dsimp [E];have : 0≤Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+51*rho0/100) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(D.ell i)) (Z^sourceLx) (Z^sourceLy) Z-
        principalPhysicalPool η S T W (fun i=>Z^(D.ell i)) W0 W1 (Z^sourceLx) (Z^sourceLy) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(D.ell i)) W0 W1 (Z^sourceLx) (Z^sourceLy) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(D.ell i)) W0 W1 (Z^sourceLx) (Z^sourceLy) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

end SevenEighths.ProbeHighRowFamily
end
end OAI
