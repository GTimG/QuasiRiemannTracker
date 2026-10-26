/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal corrected marked source at a fixed inducing character. The marked
projector remains inside its exact finite row; only surviving character terms
need the puncture and Newton count gates. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.PuncturedNewtonSupport

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentHeckeExpansion
open CenteredMomentSourceRectangleMask CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildInput CenteredMomentAbsoluteEnergy
open CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude CenteredMomentAddedZeroUniform
open CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O

/-- Full original marked polynomial, with the same corrected centered pair. -/
theorem corrected_marked_fixed_inducing_source
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ι : Type*,∀inst : Fintype ι,∀s : Input ι,
      s.W₁=(W₁:ℝ→ℂ) →s.W₂=(W₂:ℝ→ℂ) →s.b₁≤b →s.b₂≤b →
      ∀Z : ℝ,1≤Z →∀η : Character,∀R : Ideal O,R≠0 →
      ∀A z : O,A≠0 →z≠0 →
      (HeckeRowClosure.rowConductorBound η (fixedBadMask*idealGenerator R) 1 (A*z):ℝ)≤Z^Bχ →
      FixedInducingRow η Q (fixedBadMask*idealGenerator R) A z →
      ∀A₁ A₂ D K : Ideal O,A₁≠0 →A₂≠0 →D∣R →((A₁*A₂).absNorm:ℝ)≤Z^BA →
      ∀P : Finset (Ideal O),0<P.card →(∀p∈P,Prime p) →(∀p∈P,16≤p.absNorm) →
      (∀p∈P,(p.absNorm:ℝ)≤Z^Bpool) →
      (∀p∈P,∀i I,I∈s.slots i→¬p∣I) →
      2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card →
      ∀t L : ℝ,0<L →L≤s.X₁ →L≤s.X₂ →L≤s.Y₁ →L≤s.Y₂ →
      (∀n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
        frozenProfile W₁ W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0→
          (idealDividingPool P (n.1*n.2)).card≤depth) →
      ‖modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P)) R 1 η t (A*z)‖≤
        (C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          (max 1 L)^(-α)*slotControl s.toData)*volume s := by
  obtain ⟨J,S,hS,hsource⟩ := corrected_fixed_inducing_source_control
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι inst s hsW₁ hsW₂ hb₁ hb₂ Z hZ η R hR A z hA hz hcond hex
    A₁ A₂ D K hA₁ hA₂ hDR hnormA P hP hp hN hpool havoid hbudget
    t L hL hX₁ hX₂ hY₁ hY₂ hcount
  let ψ := rowWeight η (fixedBadMask*idealGenerator R) A z t
  let E := C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
    Real.sqrt (s.X₁*s.X₂)*(max 1 L)^(-α)
  have hE : 0≤E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)) (by positivity)) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hm : fixedBadMask*idealGenerator R≠0 :=
    mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R hR)
  have hml : goodLambda∣fixedBadMask*idealGenerator R :=
    (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣fixedBadMask*idealGenerator R :=
    (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hpoint (v : ∀i,s.slots i) (hv : ψ (∏i,(v i:Ideal O))≠0) :
      ‖correctedCenteredRow P D (∏i,(v i:Ideal O)) A₁ A₂ ψ
        s.W₁ s.W₂ b s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖≤E := by
    rw [hsW₁,hsW₂]
    apply hsource W₁ W₂ hs₁ hs₂ Z hZ η (fixedBadMask*idealGenerator R) A z
      hm hA hz hml hm2 hcond hex A₁ A₂ D (∏i,(v i:Ideal O)) hA₁ hA₂ hnormA P hP hp hN hpool
      (input_pool_avoids_marked s P hp havoid v) hbudget t s.X₁ s.X₂ s.Y₁ s.Y₂
      (s.X₁*s.X₂) L hL hX₁ hX₂ hY₁ hY₂ rfl s.same_product
    intro n hn hsf hf hψ
    exact punctured_newton_support η R D _ n.1 n.2 hDR A z t hv hψ P depth hp
      (input_pool_avoids_marked s P hp havoid v) (hcount n hn hsf hf) hbudget
  have he := Collision.corrected_marked_seed_one_row s P A₁ A₂ D K R hA₁ hA₂ η t (A*z) b hb₁ hb₂
  have hrow : rowWeight η (fixedBadMask*idealGenerator R) 1 (A*z) t=ψ := by
    ext I
    simp only [ψ,rowWeight,one_mul]
  simp_rw [hrow] at he
  have ht := input_marked_triangle_nonzero s K ψ
    (fun I=>rowWeight_norm_le_one_all η _ A z t I)
    (fun v=>correctedCenteredRow P D (∏i,(v i:Ideal O)) A₁ A₂ ψ
      s.W₁ s.W₂ b s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)) E hE hpoint
  have hbnd : ‖(Real.sqrt (s.X₁*s.X₂):ℂ)⁻¹*
      modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P)) R 1 η t (A*z)‖≤
      E*slotControl s.toData*(∏i,s.P i) := by
    rw [he]
    exact ht
  have hT : 0<s.X₁*s.X₂ := mul_pos s.X₁_pos s.X₂_pos
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ←div_eq_inv_mul] at hbnd
  have hbnd := (div_le_iff₀ (Real.sqrt_pos.2 hT)).mp hbnd
  apply hbnd.trans_eq
  dsimp only [E,volume]
  have hsq := Real.sq_sqrt hT.le
  calc
    _=(C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
        (max 1 L)^(-α)*slotControl s.toData)*(Real.sqrt (s.X₁*s.X₂))^2*(∏i,s.P i) := by ring
    _=_ := by rw [hsq];ring

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_marked_fixed_inducing_source
