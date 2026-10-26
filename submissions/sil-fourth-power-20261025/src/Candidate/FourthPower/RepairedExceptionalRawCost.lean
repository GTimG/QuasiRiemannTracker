/- Copyright (c) 2026 Sil. Apache-2.0.
Actual fixed-inducing supplier component at original K, now ready for
the shared RAW supplier mass theorem. The checked analytic provider is
called here. Ordinary profiles, first-live shape, and every moving
geometric quantity remain explicit. 
-/
import Candidate.FourthPower.RepairedSupplierProfiles

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedExceptionalRawCost
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentFirstAmplificationChoice
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedOriginalTail
open MixedFirstExceptionalNormalization
open OuterFreshSource OuterFreshSelected OuterFreshConsumer OuterFreshCutoffAllowance
open RepairedGroupedConsumer RepairedGroupedExceptional RepairedRawSupplier
open RepairedComponentRawCost RepairedSupplierProfiles
open CenteredMomentSectorLocalization
open OuterFreshAssembly
open MixedPrincipalCentered
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem uniform_exceptional_raw_cost (N : ℕ)
    (saving Bcap a b ε δ Bnorm Lrad Cr εsum : ℝ)
    (hs : (2/3:ℝ) ≤ saving) (hs4 : saving < 4/5) (hBcap : 0 ≤ Bcap)
    (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) (hδ : 0 < δ) (hgap : saving+2*δ < 1)
    (hBnorm : 0 ≤ Bnorm) (hLrad : 0 ≤ Lrad) (hCr : 0 < Cr) (hεsum : 0 < εsum)
    (Q : Id) (hQ0 : Q ≠ 0) (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), (0,0) ∈ control ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type u) [Fintype ι], ∀ s : Source ι a b, ∀ cover : OriginalEnclosure s,
      Fintype.card ι ≤ N →
    ∀ Kslot : ℝ, 1 ≤ Kslot → (∀ i,s.M i ≤ Kslot) →
      (∀ i,Function.support (s.Wslot i) ⊆ Icc (1:ℝ) 2) →
    ∀ (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ}),
    let q := supplierData s ha u L J
    ∀ x : Frozen q,
    let r := residualSource s ha cover u L J x;
    (r.Fhole.absNorm:ℝ) ≤ Z^Bcap → (∏ i,2*r.P i) ≤ Z^Bcap → poolCap r ≤ Z^Bnorm →
    ∀ (seed : Id) (τ : Character) (ξ χ : RayCharacter), Squarefree seed → seed ≠ 0 →
    ∀ (t K T ζ H : ℝ), 0 < K → 0 ≤ T → poolCap r ≤ H → H ≤ Z^Bnorm →
      frequencyRadius T Z ζ ≤ Cr*Z^Lrad →
      (∀ y ∈ activeSelected q,outerFamilyConductorBudget q x y r τ (frequencyRadius T Z ζ) ≤ Z^Bcap) →
    supplierFront q x * ‖selectedSum q x τ
      (fun y => fixedPart true q x y r seed τ ξ χ Q t ballProfile K T Z ζ H)‖ ≤
      (C*selectedCap N Kslot*heightBase t^(2*degree)*
        (profileEnvelope s N Kslot degree control Z ε)^2*
        shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1*
        Z^(2*Bnorm*δ+εsum))*rawSupplierCost q x seed := by
  obtain ⟨degree,control,h00,hkernel⟩ := uniform_grouped_exceptional N
    saving Bcap a b ε δ Bnorm Lrad Cr εsum
    hs hs4 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum
  obtain ⟨Ckernel,hCkernel,hq⟩ := hkernel ballProfile
  obtain ⟨A,Csum,hA,hCsum,hbound⟩ := hq Q hQ0 hQt hQ72
  let Fixed := Ckernel*A*(windowMoment degree)^2*fixedQCost Q*Csum*a^(-4/3:ℝ)
  have hFixed : 0 ≤ Fixed := by
    have hQ := fixedQCost_nonneg Q
    dsimp only [Fixed]
    positivity
  let C := 1+Fixed
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨degree,control,h00,C,hC,hbound.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι s cover hcard Kslot hKslot hM hWs u L J
  dsimp only
  intro x hF hPs hpool seed τ ξ χ
    hseed hseed0 t K T ζ H hK hT hpoolH hH hrad hcond
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  have hP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hW := selectedVolume_pos q hP
  have hCap0 : 0 ≤ selectedCap N Kslot := by
    have hk0 : 0 ≤ Kslot := zero_le_one.trans hKslot
    unfold selectedCap
    positivity
  have ht0 : 0 ≤ heightBase t := (heightBase_pos t).le
  have hV := sourceVolume_pos r
  have hz := zero_lt_one.trans hZ.1
  have he := hZ.2 ι q x r (residual_matches s ha cover u L J x)
    (residual_enclosure s ha cover u L J x) ((rest_card_le q).trans hcard) hF hPs hpool
    s.M (fun i => zero_le_one.trans (s.hM i)) (fun i I _ => s.hν i I)
    s.hWnorm hWs hP (fun i I hI => (s.hpn i I hI).2)
    seed τ ξ χ hseed hseed0 t K T ζ H hK hT hpoolH hH hrad hcond
  have he' := (div_le_iff₀ (mul_pos hW hV)).mp he
  let Lead := (Ckernel*A*heightBase t^(2*degree)*(windowMoment degree)^2)*
    fixedQCost Q*Z^(2*Bnorm*δ)*Csum*Z^εsum
  have hLead : 0 ≤ Lead := by
    have ht := (heightBase_pos t).le
    have hQ := fixedQCost_nonneg Q
    dsimp only [Lead]
    positivity
  have hraw : supplierFront q x * ‖selectedSum q x τ
      (fun y => fixedPart true q x y r seed τ ξ χ Q t ballProfile K T Z ζ H)‖ ≤
      (Lead*selectedMass q s.M*(sourceProfile r degree control Z ε)^2)*
        (supplierFront q x*(selectedVolume q*sourceVolume r*commonPhysicalCost r K /
          ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ)))) := by
    apply (mul_le_mul_of_nonneg_left he' (supplierFront_nonneg q x)).trans_eq
    dsimp only [Lead]
    unfold sourcePrefactor
    ring
  have hprof := residual_sourceProfile_le s ha cover u L J x N hcard Kslot hKslot hM
    degree control Z ε hz.le
  have hprofile0 : 0 ≤ sourceProfile r degree control Z ε := by
    have h₁ := sourceControl_nonneg control r.W₁
    have h₂ := sourceControl_nonneg control r.W₂
    have hm := MixedPrincipalBudget.fullMarkedCost_nonneg r
    unfold sourceProfile
    positivity
  have hprofSq := pow_le_pow_left₀ hprofile0 hprof 2
  have hmass := selectedMass_le s ha u L J N hcard Kslot hKslot hM
  have hcost := rawSupplierCost_nonneg q hP x seed
  have hshape : 0 ≤ shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1 := by
    have hv := sourceVolume_pos s
    have hp := pairNorm_pos s.hd.1 s.hd.2
    have hh := prefixNormMax_pos s.d s.hd
    have hl := s.hL
    unfold shape
    positivity
  have hgeom := exceptional_le_raw_cost s ha cover u L J x seed K hK
  have hwhole := hraw.trans (mul_le_mul_of_nonneg_left hgeom
    (mul_nonneg (mul_nonneg hLead (selectedMass_nonneg q s.M)) (sq_nonneg _)))
  have hcoarse : supplierFront q x * ‖selectedSum q x τ
      (fun y => fixedPart true q x y r seed τ ξ χ Q t ballProfile K T Z ζ H)‖ ≤
      (Lead*selectedCap N Kslot*(profileEnvelope s N Kslot degree control Z ε)^2)*
        ((a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
          rawSupplierCost q x seed) := by
    apply hwhole.trans
    gcongr
  have hpowers : Z^(2*Bnorm*δ)*Z^εsum = Z^(2*Bnorm*δ+εsum) :=
    (Real.rpow_add hz _ _).symm
  have hfinal : supplierFront q x * ‖selectedSum q x τ
      (fun y => fixedPart true q x y r seed τ ξ χ Q t ballProfile K T Z ζ H)‖ ≤
      (Fixed*selectedCap N Kslot*heightBase t^(2*degree)*
        (profileEnvelope s N Kslot degree control Z ε)^2*
        shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1*
        Z^(2*Bnorm*δ+εsum))*rawSupplierCost q x seed := by
    apply hcoarse.trans_eq
    dsimp only [Lead,Fixed]
    rw [← hpowers]
    ring
  apply hfinal.trans
  have hFC : Fixed ≤ C := by dsimp only [C]; linarith
  gcongr

end
end Candidate.FourthPower.RepairedExceptionalRawCost
