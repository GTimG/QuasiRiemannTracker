/- Copyright (c) 2026 Sil. Apache-2.0.
Actual original-scale second zero and tail, expressed directly in the
shared rawSupplierCost. This retains the complete supplier Cauchy mass.
Subunit sharp support is handled by exact vanishing. 
-/
import Candidate.FourthPower.RepairedSupplierProfiles

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedRemainderRawCost
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge ActualEisensteinCubic EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open OuterFreshSource OuterFreshSelected OuterFreshConsumer OuterFreshCompletion OuterFreshCutoffAllowance
open RepairedGroupedConsumer RepairedRemainderGeometry RepairedRawSupplier
open RepairedComponentRawCost RepairedSupplierProfiles
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem uniform_zero_raw_cost (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type u) [Fintype ι], ∀ a b : ℝ, ∀ s : Source ι a b,
    ∀ ha : 0 < a, ∀ cover : OriginalEnclosure s, Fintype.card ι ≤ N →
    ∀ Kslot : ℝ, 1 ≤ Kslot → (∀ i,s.M i ≤ Kslot) →
    ∀ (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ}),
    let q := supplierData s ha u L J
    ∀ x : Frozen q, ∀ seed : Id, seed ≠ 0 →
    ∀ (τ : Character) (ξ : RayCharacter) (t K Z B : ℝ), 0 ≤ K → 1 < Z →
    let r := residualSource s ha cover u L J x;
    sourceNormCap r.P b r.T r.d ≤ Z^B →
    supplierFront q x * ‖selectedSum q x τ (fun y => outerZero q x y r seed τ ξ t K)‖ ≤
      (C*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap s)^2*
        (2:ℝ)^N*b^2*K*selectedVolume q*(sourceVolume s/pairNorm s.d)*Z^(B*ε))*
          rawSupplierCost q x seed := by
  obtain ⟨C,hC,hzero⟩ := uniform_average_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι instι a b s ha cover hcard Kslot hKslot hM u L J
  dsimp only
  intro x seed hseed τ ξ t K Z B hK hZ hcap
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  let Y := sourceNormCap r.P b r.T r.d
  change supplierFront q x * ‖selectedSum q x τ (fun y => outerZero q x y r seed τ ξ t K)‖ ≤ _
  have hCap0 : 0 ≤ selectedCap N Kslot := by
    have hk0 : 0 ≤ Kslot := zero_le_one.trans hKslot
    unfold selectedCap
    positivity
  have hP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hW := selectedVolume_pos q hP
  have hMass := selectedMass_nonneg q s.M
  have hProf := profileCap_nonneg s
  have hProfR := profileCap_nonneg r
  have hz := zero_lt_one.trans hZ
  have hcost := rawSupplierCost_nonneg q hP x seed
  have hdim := (rest_card_le q).trans hcard
  by_cases hY : 1 ≤ Y
  · have hY0 := zero_lt_one.trans_le hY
    have he := hzero ι q x a b r hdim ha (residual_matches s ha cover u L J x) s.M
      (fun i => zero_le_one.trans (s.hM i)) (fun i I _ => s.hν i I) s.hWnorm hP
      (fun i I hI => (s.hpn i I hI).2) seed ξ τ t K Y hseed hK hY le_rfl
    have hg := (RepairedRemainderGeometry.grouped_norm_le_average q x τ hP
      (fun y => outerZero q x y r seed τ ξ t K)).trans
      (mul_le_mul_of_nonneg_left he hW.le)
    have hprof : (profileCap r)^2 ≤ (profileCap s)^2 :=
      pow_le_pow_left₀ hProfR (residual_profileCap_le s ha cover u L J x) 2
    have hpower : Y^(1+ε) ≤ Y*Z^(B*ε) := by
      rw [Real.rpow_add hY0,Real.rpow_one]
      apply mul_le_mul_of_nonneg_left _ hY0.le
      exact (Real.rpow_le_rpow hY0.le hcap hε.le).trans_eq (by rw [← Real.rpow_mul hz.le])
    have hg' : ‖selectedSum q x τ (fun y => outerZero q x y r seed τ ξ t K)‖ ≤
        (selectedMass q s.M*‖paperRadialFourier ballProfile 0‖*C*(profileCap s)^2*Z^(B*ε))*
          (selectedVolume q*K*Y/(seed.absNorm:ℝ)) := by
      apply hg.trans
      calc
        _ ≤ selectedVolume q*(selectedMass q s.M*
            (K*‖paperRadialFourier ballProfile 0‖*(C*(profileCap s)^2*(Y*Z^(B*ε))/(seed.absNorm:ℝ)))) := by
          gcongr
        _ = _ := by ring
    let Lead := selectedMass q s.M*‖paperRadialFourier ballProfile 0‖*C*(profileCap s)^2*Z^(B*ε)
    have hLead : 0 ≤ Lead := by dsimp only [Lead]; positivity
    have hr := zero_le_raw_cost s ha cover u L J x seed K hK
    have hraw : supplierFront q x * ‖selectedSum q x τ (fun y => outerZero q x y r seed τ ξ t K)‖ ≤
        Lead*((b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*selectedVolume q*(sourceVolume s/pairNorm s.d))*
          rawSupplierCost q x seed) := by
      calc
        _ ≤ supplierFront q x*(Lead*(selectedVolume q*K*Y/(seed.absNorm:ℝ))) :=
          mul_le_mul_of_nonneg_left hg' (supplierFront_nonneg q x)
        _ = Lead*(supplierFront q x*(selectedVolume q*K*Y/(seed.absNorm:ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hr hLead
    have hm := selectedMass_le s ha u L J N hcard Kslot hKslot hM
    have hd : (2:ℝ)^Fintype.card (RestIndex q) ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hdim
    apply hraw.trans
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    have hv := (sourceVolume_pos s).le
    dsimp only [Lead]
    calc
      _ ≤ (selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*C*(profileCap s)^2*Z^(B*ε))*
          ((b^2*(2:ℝ)^N*K*selectedVolume q*(sourceVolume s/pairNorm s.d))*rawSupplierCost q x seed) := by
        gcongr
      _ = _ := by ring
  · have hterm (y : Selected q) : outerZero q x y r seed τ ξ t K = 0 :=
      outer_zero_of_cap_lt_one q x y r ha (residual_matches s ha cover u L J x)
        seed ξ τ t K (lt_of_not_ge hY)
    simp only [selectedSum,hterm,mul_zero,Finset.sum_const_zero,norm_zero,mul_zero]
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    have hv := (sourceVolume_pos s).le
    unfold selectedCap
    positivity

/-- Tail coefficient includes the actual raw-cost ratio cap. The
underlying arbitrary-saving theorem is invoked with saving+Bratio. -/
theorem uniform_tail_raw_cost (N : ℕ) (B Bratio ζ saving : ℝ) (hB : 0 ≤ B) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type u) [Fintype ι], ∀ a b : ℝ, ∀ s : Source ι a b,
    ∀ ha : 0 < a, 0 ≤ b → ∀ cover : OriginalEnclosure s, Fintype.card ι ≤ N →
    ∀ Kslot : ℝ, 1 ≤ Kslot → (∀ i,s.M i ≤ Kslot) →
    ∀ (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ}),
    let q := supplierData s ha u L J
    ∀ x : Frozen q, ∀ seed : Id, seed ≠ 0 →
      frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ) ≤ Z^Bratio →
    let r := residualSource s ha cover u L J x
    ∀ (ξ : RayCharacter) (τ : Character) (t K X T : ℝ),
      0 < K → 0 < X → poolCap r ≤ Z^B → sourceNormCap r.P b r.T r.d ≤ X →
      X ≤ Z^B → K ≤ Z^B → T ≤ Z^B → X^2/K ≤ T →
    supplierFront q x * ‖selectedSum q x τ (fun y => secondDiscardedEnergy τ t (sourceColumns r)
      (outerColumn q x y seed ξ) ballProfile K T Z ζ)‖ ≤
      (C*selectedCap N Kslot*(profileCap s)^2*Z^(-saving))*rawSupplierCost q x seed := by
  obtain ⟨control,C,hC,htail⟩ := uniform_average_tail B ζ (saving+Bratio) hB hζ
  let seminorm := control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  have hsemi : 0 ≤ seminorm := apply_nonneg _ _
  let Ctail := 1+C*seminorm
  have hCt : 0 < Ctail := by dsimp only [Ctail]; positivity
  have hCC : C*seminorm ≤ Ctail := by dsimp only [Ctail]; linarith
  refine ⟨Ctail,hCt,htail.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a b s ha hb cover hcard Kslot hKslot hM u L J
  dsimp only
  intro x seed hseed hratio
    ξ τ t K X T hK hX hpool hsupport hXcap hKcap hTcap hcutoff
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  have hP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hW := selectedVolume_pos q hP
  have hMass := selectedMass_nonneg q s.M
  have hProf := profileCap_nonneg s
  have hProfR := profileCap_nonneg r
  have hz := zero_lt_one.trans hZ.1
  have he := hZ.2 ι q x a b r ha hb (residual_matches s ha cover u L J x) s.M
    (fun i => zero_le_one.trans (s.hM i)) (fun i I _ => s.hν i I) s.hWnorm hP
    (fun i I hI => (s.hpn i I hI).2) seed ξ τ t K X T hK hX hpool hsupport
    hXcap hKcap hTcap hcutoff
  have hg := (RepairedRemainderGeometry.grouped_norm_le_average q x τ hP
    (fun y => secondDiscardedEnergy τ t (sourceColumns r) (outerColumn q x y seed ξ) ballProfile K T Z ζ)).trans
      (mul_le_mul_of_nonneg_left he hW.le)
  have hprof := pow_le_pow_left₀ hProfR (residual_profileCap_le s ha cover u L J x) 2
  have hm := selectedMass_le s ha u L J N hcard Kslot hKslot hM
  let Lead := Ctail*selectedCap N Kslot*(profileCap s)^2
  have hCap0 : 0 ≤ selectedCap N Kslot := by
    have hk0 : 0 ≤ Kslot := zero_le_one.trans hKslot
    unfold selectedCap
    positivity
  have hLead : 0 ≤ Lead := by dsimp only [Lead,selectedCap]; positivity
  have hg' : ‖selectedSum q x τ
      (fun y => secondDiscardedEnergy τ t (sourceColumns r) (outerColumn q x y seed ξ) ballProfile K T Z ζ)‖ ≤
      Lead*selectedVolume q*Z^(-(saving+Bratio)) := by
    apply hg.trans
    calc
      _ = selectedVolume q*selectedMass q s.M*(C*seminorm)*(profileCap r)^2*Z^(-(saving+Bratio)) := by
        dsimp only [seminorm]
        ring
      _ ≤ selectedVolume q*selectedCap N Kslot*Ctail*(profileCap s)^2*Z^(-(saving+Bratio)) := by
        gcongr
      _ = _ := by dsimp only [Lead]; ring
  have hgeom := tail_le_raw_cost q hP x seed hseed Z Bratio saving hZ.1 hratio
  calc
    _ ≤ supplierFront q x*(Lead*selectedVolume q*Z^(-(saving+Bratio))) :=
      mul_le_mul_of_nonneg_left hg' (supplierFront_nonneg q x)
    _ = Lead*(supplierFront q x*selectedVolume q*Z^(-(saving+Bratio))) := by ring
    _ ≤ Lead*(Z^(-saving)*rawSupplierCost q x seed) := mul_le_mul_of_nonneg_left hgeom hLead
    _ = _ := by dsimp only [Lead]; ring

end
end Candidate.FourthPower.RepairedRemainderRawCost
