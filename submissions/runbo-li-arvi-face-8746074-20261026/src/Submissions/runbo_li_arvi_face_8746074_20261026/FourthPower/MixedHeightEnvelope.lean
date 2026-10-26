/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform polynomial control of the common height shift in the actual
restricted original source. The divisor norms remain explicit.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedOriginalSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedHeightEnvelope
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedOriginalSource MixedLiveNormalization MixedSourceAssembly
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentEnergyProfiles
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The base height uses the same angular frequency units as the
independent-profile seminorm theorem. It is independent of the new
column-height variable v. -/
def sourceHeight (t V t₁ t₂ : ℝ) : ℝ :=
  1+|t|+V+|2*Real.pi*t₁|+|2*Real.pi*t₂|

theorem sourceHeight_one_le (t V t₁ t₂ : ℝ) (hV : 0≤V) :
    1≤sourceHeight t V t₁ t₂ := by
  unfold sourceHeight
  linarith [abs_nonneg t,abs_nonneg (2*Real.pi*t₁),abs_nonneg (2*Real.pi*t₂)]

/-- Ordinary-profile seminorms and the marked-slot height polynomial
have a common polynomial envelope under simultaneous height shifts.
Its degree, seminorm set, and constant precede every height parameter. -/
theorem shifted_profile_height (a b : ℝ) (ha : 0<a) (S : Finset (ℕ×ℕ)) (degree : ℕ) :
    ∃J : ℕ,∃U : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀t V t₁ t₂ v : ℝ,0≤V →
      ((independentProfiles ha W₁ W₂ hs₁ hs₂
        (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))).control S)^2*
        (1+|t+v|+V)^degree ≤
      C*(sourceControl U W₁*sourceControl U W₂)^2*
        (sourceHeight t V t₁ t₂)^J*(1+|v|)^J := by
  obtain ⟨n,U,Cp,hCp,hprofile⟩ := independent_profile_control a b ha S
  refine ⟨degree+4*n,U,Cp^2*2^(4*n),by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ t V t₁ t₂ v hV
  let A := sourceControl U W₁*sourceControl U W₂
  let H := sourceHeight t V t₁ t₂
  let B := 1+|v|
  have hA : 0≤A := mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hH : 1≤H := sourceHeight_one_le t V t₁ t₂ hV
  have hH0 : 0≤H := zero_le_one.trans hH
  have hB : 0≤B := by dsimp only [B];positivity
  have hf (u : ℝ) : 2*Real.pi*(u+v/(2*Real.pi))=2*Real.pi*u+v := by
    field_simp [Real.pi_ne_zero]
  have hfreq : 1+‖2*Real.pi*(t₁+v/(2*Real.pi))‖+
      ‖2*Real.pi*(t₂+v/(2*Real.pi))‖≤2*H*B := by
    rw [hf,hf]
    simp only [Real.norm_eq_abs]
    have hmain : 1+|2*Real.pi*t₁|+|2*Real.pi*t₂|≤H := by
      dsimp only [H,sourceHeight]
      linarith [abs_nonneg t]
    have hmul := mul_nonneg (sub_nonneg.mpr hH) (abs_nonneg v)
    dsimp only [B]
    nlinarith [abs_add_le (2*Real.pi*t₁) v,abs_add_le (2*Real.pi*t₂) v]
  have hheight : 1+|t+v|+V≤H*B := by
    have hmain : 1+|t|+V≤H := by
      dsimp only [H,sourceHeight]
      linarith [abs_nonneg (2*Real.pi*t₁),abs_nonneg (2*Real.pi*t₂)]
    have hmul := mul_nonneg (sub_nonneg.mpr hH) (abs_nonneg v)
    dsimp only [B]
    nlinarith [abs_add_le t v]
  have hp := (hprofile W₁ W₂ hs₁ hs₂
    (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfreq (2*n))
        (mul_nonneg hCp.le hA))
  have hp0 := (independentProfiles ha W₁ W₂ hs₁ hs₂
    (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))).control_nonneg S
  have hsq := pow_le_pow_left₀ hp0 hp 2
  have hpow := pow_le_pow_left₀ (show 0≤1+|t+v|+V by positivity) hheight degree
  calc
    _ ≤ (Cp*A*(2*H*B)^(2*n))^2*(H*B)^degree :=
      mul_le_mul hsq hpow (by positivity) (sq_nonneg _)
    _ = _ := by
      change _=(Cp^2*2^(4*n))*A^2*H^(degree+4*n)*B^(degree+4*n)
      rw [mul_pow,mul_pow,←pow_mul,show (2*n)*2=4*n by omega]
      simp only [mul_pow,pow_add]
      ring

variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- A proved all-height envelope for the actual shifted original row.
The norms of both divisors and the ordinary prefix remain explicit;
they are not silently charged to a power of Z. -/
theorem uniform_shifted_original_source
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
      radialEnergy (fun z=>originalMaskedRow (naturalCharacter s.character z)
        (enclosure (Cap*Z^Lcap)) H (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
        d hd G R seed D hG
        (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ (t+v))
        (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
        (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi))) b X₁ X₂ Y₁ Y₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
        diagonalControl s.radial.profile*
        (sourceControl control W₁*sourceControl control W₂)^2*
        (sourceHeight t V t₁ t₂)^degree*(1+|v|)^degree*
        Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,S,hbase⟩ := uniform_original_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hδ hβ hκ Q hQt hQ72 hQM
  obtain ⟨J,U,Cp,hCp,hprofile⟩ := shifted_profile_height a b ha S degree
  refine ⟨J,U,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C*Cp,mul_pos hC hCp,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  have he := hZ.2 θ w σ freq (t+v) V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD H hH hcap hHR W₁ W₂ hs₁ hs₂
    (t₁+v/(2*Real.pi)) (t₂+v/(2*Real.pi)) X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  have hp := hprofile W₁ W₂ hs₁ hs₂ t V t₁ t₂ v hV
  let F := (C*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
    diagonalControl s.radial.profile
  have hF : 0≤F := by
    have := diagonalControl_nonneg s.radial.profile
    have := pairNorm_pos hd.1 hd.2
    dsimp only [F]
    positivity
  apply he.trans
  calc
    _ = F*(((independentProfiles ha W₁ W₂ hs₁ hs₂
        (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))).control S)^2*
        (1+|t+v|+V)^degree)*Z^(s.width+κ*(∑i,w i)+ε) := by dsimp only [F];ring
    _ ≤ F*(Cp*(sourceControl U W₁*sourceControl U W₂)^2*
        (sourceHeight t V t₁ t₂)^J*(1+|v|)^J)*Z^(s.width+κ*(∑i,w i)+ε) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hF)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
    _ = _ := by dsimp only [F];ring

end
end Candidate.FourthPower.MixedHeightEnvelope
