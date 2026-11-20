/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairHighSelectedIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

open QRH.Record12518109Source QRH.Record12518109Existence

open CenteredMomentEnergyState Qrh.JointDetector

/-- Genuine high measured-response source for two completely independent
ordinary factors. The original response and every original normalized slot
are retained, including zero widths. The exact saving is .0305 minus any
requested positive loss; controls and height degree precede every live datum. -/
theorem high_selected_pair_source_zero_degree {n y : ℝ}
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn1 : n ≤ sourceRatio*y)
    (amax loss : ℝ) (ha : 1 ≤ amax) (hloss : 0 < loss) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (W : ℝ→ℂ),Continuous W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ buffer Cslot : ℝ,0 < buffer → 0 < Cslot →
    ∀ old base : Character,
    ∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ amax →
    ∀ (J : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
      (tOld t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ i) → (∀ i,σ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∑ i∈J,w i) ≤ sourceWidth n y →
    ∀ (η₁ η₂ : Character) (Q₁ Q₂ : Ideal O),
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow),
      (∀ z∈s,initialKeep η₁ Q₁ z.val) → (∀ z∈s,initialKeep η₂ Q₂ z.val) →
      (∀ z∈s,rowNorm z ≤ U^V) →
      (∀ z∈s,(5002/10000:ℝ) < LowActual.originalResponse old (fixedBadMask*idealGenerator 1) 1
        tOld U (Cslot*U^buffer) (fun i:J=>w i.val)
        (originalPools rayM Hr 2 U (fun i:J=>w i.val))
        (originalCoefficients rayM Hr hHr base (fun i:J=>θ i.val) W U
          (fun i:J=>w i.val) (fun i:J=>σ i.val) (fun i:J=>v i.val))
        (fun i:J=>U^(w i.val)) z.val) →
      finiteEnergyOn J s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
        (originalMark rayM Hr hHr old base θ W U w σ v tOld) ≤
        C*(p.control {(0,0)})^2*U^(V-305/10000+loss) := by
  obtain ⟨mesh,hm,hsource⟩:=MeasuredPair.energy amax loss ha hloss
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ W hW hWs buffer Cslot hb hCslot old base
  obtain ⟨C,hC,hsource⟩:=hsource Slot W hW hWs (buffer/4) (by positivity)
  obtain ⟨bΦ,hbΦ,hΦs⟩:=radialMajorant_support_bound
  let controls : Finset (ℕ×ℕ):={(0,0)}
  refine ⟨C,hC,?_⟩
  have hmod:=eventually_ge_atTop (old.modulus.absNorm:ℝ)
  have hlarge:=(tendsto_rpow_atTop (by positivity : (0:ℝ) < buffer/2)).eventually
    (eventually_ge_atTop (1/Cslot))
  filter_upwards [hsource,hmod,hlarge] with U hsource hmod hlarge
  obtain ⟨hU,hsource⟩:=hsource
  intro rayM _ Hr hHr V hV0 hV1 J θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hwidth
    η₁ η₂ Q₁ Q₂ p X₁ X₂ hX₁ hX₂ hXN hXY s hk₁ hk₂ hy hresponse
  have hUp : 0 < U:=zero_lt_one.trans hU
  have hV : 0 ≤ V:=by linarith
  have hη : (old.modulus.absNorm:ℝ) ≤ U^(1:ℝ):=by simpa only [Real.rpow_one] using hmod
  let st:=LowActual.regularState old (⊥:Ideal O) radialMajorant bΦ U V 1 hU.le hV zero_le_one
    hΦs radialMajorant_nonneg hη
  have hpay : U^(2*(buffer/4)) ≤ Cslot*U^buffer:=by
    have hone : 1 ≤ Cslot*U^(buffer/2):=by
      simpa only [mul_comm] using (div_le_iff₀ hCslot).mp hlarge
    calc
      _ = U^(buffer/2):=by congr 1; ring
      _ ≤ U^(buffer/2)*(Cslot*U^(buffer/2)):=le_mul_of_one_le_right (by positivity) hone
      _ = _:=by rw [show buffer=buffer/2+buffer/2 by ring,Real.rpow_add hUp]; ring
  have hY : 1 ≤ U^V:=Real.one_le_rpow hU.le hV
  have hYa:=Real.rpow_le_rpow_of_exponent_le hU.le hV1
  have hbox : Box n y (sourceWidth n y) (length U X₁) (length U X₂) (∑ i∈J,w i):=
    ⟨length_nonneg _ _ hU,length_nonneg _ _ hU,Or.inl ⟨hXN,hXY⟩,
      Finset.sum_nonneg (fun i _=>hw i),hwidth⟩
  have hcap : X₁*X₂*U^(∑ i:J,w i.val) ≤ U^(9179599/10000000:ℝ):=by
    rw [Finset.sum_coe_sort]
    exact MeasuredBall.support_cap hU hX₁ hX₂ hy0 hy1 hn1 hbox
  have hprofile (j : Fin 2) (x : ℝ) : ‖p.profile j x‖ ≤ sourceControl controls (p.profile j):=by
    apply (SchwartzMap.norm_le_seminorm ℝ (p.profile j) x).trans
    exact Seminorm.le_def.mp
      (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [controls] : (0,0)∈controls)) (p.profile j)
  have hLam : goodLambda ∣ fixedBadMask:=dvd_mul_right _ _
  have htwo : (2:O) ∣ fixedBadMask:=dvd_mul_left _ _
  have hE:=hsource rayM Hr hHr bΦ st base J
    (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>v i.val) tOld mesh (Cslot*U^buffer)
    V (U^V) highRootOne s hm.le le_rfl (fun i=>hw i.val) (fun i=>hwm i.val)
    (fun i=>⟨hσlo i.val,hσhi i.val⟩) hpay
    (fun z hz=>by
      rw [high_selected_measuredResponse_eq rayM Hr hHr st old base rfl rfl W J θ w σ v tOld (Cslot*U^buffer) z]
      exact hresponse z hz) hV0 hY hYa le_rfl hy
    η₁ η₂ (fixedBadMask*idealGenerator 1) 1 1 (hLam.trans (dvd_mul_right _ _)) (htwo.trans (dvd_mul_right _ _))
    (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
    (sourceControl controls (p.profile 0)) (sourceControl controls (p.profile 1)) hX₁ hX₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2)
    (fun I _=>hprofile 0 ((I.absNorm:ℝ)/X₁)) (fun I _=>hprofile 1 ((I.absNorm:ℝ)/X₂)) hcap
  simp_rw [high_selected_slotMass_eq rayM Hr hHr st old base rfl rfl W J θ w σ v tOld] at hE
  simp only [high_rowMap_one] at hE
  convert hE using 1 <;> dsimp [finiteEnergyOn,Profiles.control,controls] <;> ring

#print axioms high_selected_pair_source_zero_degree
end
end QRH.Cycle092.StrongPair
