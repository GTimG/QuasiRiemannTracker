import Candidate.Cycle63.Physical.FirstBranches.RawComparison
import Candidate.Cycle63.Moment.InitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget

/- Original module: Candidate.Target830.Source.Assembly.ComparisonGeometry. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.AssemblyComparison
noncomputable section
open HeckeFamily CenteredMomentEnergyReferenceState
theorem actual_comparison_powers (Z M n₁ n₂ : ℝ) (hZ : 1< Z) (hM : 0≤ M)
    (hn₁ : (81/200)*M≤ n₁) (hn₂ : (81/200)*M≤ n₂)
    (hn₁' : n₁≤(44/100)*M) (hn₂' : n₂≤(44/100)*M) :
    CenteredMomentEnergyReferenceState.comparisonSecond Z M (Z^n₁) (Z^n₂) =
      Z^(n₁+n₂-M/4) ∧ M/2≤ n₁+n₂-M/4 ∧ n₁+n₂-M/4≤(63/100)*M := by
  refine ⟨?_,by linarith,by linarith⟩
  unfold CenteredMomentEnergyReferenceState.comparisonSecond
    CenteredMomentEnergyReferenceState.comparisonFirst
  rw [←Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_sub (zero_lt_one.trans hZ)]

end
end OAI.SevenEighths.Target830.Source.AssemblyComparison
#print axioms OAI.SevenEighths.Target830.Source.AssemblyComparison.actual_comparison_powers
end

/- Original module: Candidate.Target830.Source.Assembly.FixedComparison. -/
section

namespace OAI.SevenEighths.Target830.Source.AssemblyComparison
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalRowSource CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceScalarReserve CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskEnergy
open Cycle63Moment Cycle63FirstGeometry
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

open OAI.SevenEighths.Cycle63FirstActual

/-- The actual fixed-parent comparison cut. Its constants and derivative set are
chosen before the live anchor, row width, plain scales, profiles and heights.
The logarithmic conductor and arbitrarily decaying reflection tail are absorbed
into the requested loss. The original terminal is used only on daughters. -/
theorem actual_fixed_parent_comparison_fixed_mesh
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    0< comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (81/200)*M≤ n₁ → (81/200)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀u t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false (p.profile 1)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) 0 u *
      polynomial (naturalCharacter s.character z) false (p.profile 0) (comparisonFirst Z M) 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool rayM H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  have hMax : 0< Mmax := hMmin.trans_le hMmax
  let Mcap := 2*Mmax+1
  have hCap : 0< Mcap := by dsimp [Mcap]; positivity
  let d := comparisonD Mmax ε
  let xi := comparisonXi Mmin
  let L := comparisonL Mmin Mmax
  let saving := 2*Mcap+2*Mcap*d+1
  have hd : 0< d := by dsimp [d,comparisonD]; positivity
  have hxi : 0< xi := by dsimp [xi,comparisonXi]; positivity
  have hLpos : 0≤ L := by dsimp [L,comparisonL]; positivity
  have hxirho : xi≤ Mmin/100 := le_rfl
  have hL : Mcap+0+xi≤ L := by dsimp [L,comparisonL,Mcap]; linarith
  have hmain : d*(0+Mcap+2)≤ε/2 := by
    dsimp [d,comparisonD,Mcap]
    have hp : 0<4*(2*Mmax+1+2) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have herr : 0*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε/2 := by
    dsimp [saving]
    nlinarith [mul_nonneg hCap.le hd.le]
  obtain ⟨Cscalar,hCs,hscalar⟩ := ledger_bound Mcap 0 bΦ L d saving (ε/2)
    hCap.le (by norm_num) hLpos hd hmain herr
  obtain ⟨degree,n,T,Dchild,hDc,nlong,Slong,Cref,Dref,hCr,hDr,href⟩ :=
    actual_reflected_comparison rayM H hH Fmax Wslot aslot bslot lo hi
      haslot hsSlot hWslot hbslot a b bΦ d xi saving 0 L Mcap d
      ha hlo hhi hbΦ hd hxi (by norm_num) hCap hd (by linarith) hbeta hκbeta 2 (by norm_num)
  obtain ⟨J,S,Cprofile,hCp,hprofile⟩ := reference_envelopes a b ha ∅ T Slong
    degree n nlong Cref Dchild Dref hCr hDc hDr
  let delta := min 1 (ε/(2*Mmax))
  have hdelta : 0< delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta≤1 := min_le_left _ _
  have hdε : delta*Mmax≤ε/2 := by
    have hd' := min_le_right (1:ℝ) (ε/(2*Mmax))
    have hh := mul_le_mul_of_nonneg_right hd' hMax.le
    dsimp only [delta]
    field_simp at hh ⊢
    nlinarith
  refine ⟨comparisonMesh_pos Mmin Mmax ε hMmin hMmax hε, J,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨K,hK,ht⟩ := href η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cprofile*Cscalar*(K+1),by positivity,?_⟩
  filter_upwards [ht,fixed_anchor_width_uniform anchors Mmin delta hMmin hdelta] with Z hz hanchor
  refine ⟨hz.1,?_⟩
  intro j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ w σ freq
    u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hwanchor := hanchor.2 j M hmin
  have hs : s.width≤ Mcap := by
    have hh := mul_le_mul_of_nonneg_right hd1 hM
    change M+Real.logb Z ((anchors j).modulus.absNorm:ℝ)≤ Mcap
    dsimp only [Mcap]; linarith
  have hwidth : s.width≤ M+ε/2 := by
    have hh := mul_le_mul_of_nonneg_left hmax hdelta.le
    change M+Real.logb Z ((anchors j).modulus.absNorm:ℝ)≤ M+ε/2
    linarith
  have hMw : M≤ s.width := by
    change M≤ M+s.characterWidth
    exact le_add_of_nonneg_right s.character_nonneg
  have hpad : xi≤7*M/100 := by linarith
  obtain ⟨hsecond,hlong,_⟩ := actual_comparison_powers Z M n₁ n₂ hZ hM hn₁ hn₂ hn₁' hn₂'
  have hh := hz.2 F hF θ w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq
    s rfl hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
    M (n₁+n₂-M/4) (M/4) hM hMw hlong le_rfl hslots hpad
  dsimp only at hh
  let v := |u|+|t|
  have hv : 0≤ v := by dsimp [v]; positivity
  have hp := hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) v height hheight
  dsimp only at hp
  simp only [abs_of_nonneg hv] at hp
  simp only [v,←add_assoc] at hp
  change _ ∧ _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J ∧
    _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J at hp
  have hu : 1+‖u‖≤1+‖v‖ := by simp only [Real.norm_eq_abs,abs_of_nonneg hv]; dsimp [v]; linarith [abs_nonneg t]
  have ht' : 1+|t|+height≤1+|v|+height := by rw [abs_of_nonneg hv]; dsimp [v]; linarith [abs_nonneg u]
  let A := Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J
  let E := (K+1)*diagonalControl Φ*A
  have hdiag : 0≤ diagonalControl Φ := by unfold diagonalControl; positivity
  have hA : 0≤ A := by dsimp [A]; positivity
  have hE : 0≤ E := by dsimp [E]; positivity
  have hmain : Cref*(sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
      (K*diagonalControl Φ*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|+height)^(degree+2*n))≤ E := by
    have hp' : Cref*Dchild*(sourceControl Slong (p.profile 1))^2*
        (sourceControl T (p.profile 0))^2*(1+‖u‖)^(2*nlong)*
        (1+|t|+height)^(degree+2*n)≤ A := by
      apply le_trans _ hp.2.1
      gcongr
      linarith [abs_nonneg u,abs_nonneg t]
    have hmul := mul_le_mul_of_nonneg_left hp' (mul_nonneg hK.le hdiag)
    have hk : K*diagonalControl Φ*A≤ E := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul_of_nonneg_right (by linarith) hdiag
    apply le_trans _ hk
    convert hmul using 1; ring
  have herr : Dref*(sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl Φ≤ E := by
    have hp' : Dref*(sourceControl Slong (p.profile 1))^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖u‖)^(2*nlong)≤ A := by
      apply le_trans _ hp.2.2
      gcongr
    have hmul := mul_le_mul_of_nonneg_left hp' hdiag
    have hk : diagonalControl Φ*A≤ E := by
      calc
        _ = 1*diagonalControl Φ*A := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hdiag) hA
    apply le_trans _ hk
    convert hmul using 1; ring
  have hsum : (∑i : F,w i)≤ Mcap := by
    rw [Finset.sum_coe_sort]
    linarith
  have hledger := hscalar Z hZ.le s hs F (fun i => w i) hsum
  have hrad : (s.puncture.radical.absNorm:ℝ)^d=1 := by
    change (((1:Ideal O).radical).absNorm:ℝ)^d=1
    simp [Ideal.radical_top,Ideal.absNorm_top]
  rw [hrad,one_mul] at hledger
  rw [Finset.prod_coe_sort F (fun i => Z^(w i))] at hledger
  have hlog : 0≤ Real.log Z := (Real.log_pos hZ).le
  have hL0 : 0≤ L := by linarith
  have hwindow : max 0 (s.width-(n₁+n₂-M/4)+xi)≤ L := max_le hL0 (by linarith)
  have hshort : Z^(M/4)≤ Z^(s.width/4) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  let P := Z^(s.width+d)
  let Qmain := (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
    (1+2*(L*Real.log Z))*P
  let Qerror := (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i∈F,Z^(w i))
  have hP : 0≤ P := by dsimp [P]; positivity
  have hQm : 0≤ Qmain := by dsimp [Qmain]; positivity
  have hQe : 0≤ Qerror := by dsimp [Qerror]; positivity
  have htotal : _ ≤ E*Qmain+E*Qerror := add_le_add
    (mul_le_mul_of_nonneg_right hmain hQm) (mul_le_mul_of_nonneg_right herr hQe)
  have hbound : E*Qmain+E*Qerror ≤ E*(P+Qmain+Qerror) := by nlinarith only [mul_nonneg hE hP]
  have hlast := mul_le_mul_of_nonneg_left hledger hE
  dsimp only
  rw [hsecond]
  change _ ≤ _ at hh
  apply hh.trans
  apply le_trans _ (le_trans htotal (le_trans hbound (hlast.trans ?_)))
  · dsimp [Qmain,Qerror,P]
    calc
      _ ≤ Cref*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl Φ*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+d)) +
        Dref*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          (sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
          diagonalControl Φ*max 1 s.radial.scale*Z^(s.width/4)*(∏i∈F,Z^(w i)) := by
        gcongr <;> rfl
      _ = _ := by simp only [Real.norm_eq_abs,schwartzSeminormFamily]; ring
  · dsimp [E,A]
    have hzpow := Real.rpow_le_rpow_of_exponent_le hZ.le (show s.width+ε/2≤ M+ε by linarith)
    have hm := mul_le_mul_of_nonneg_left hzpow
      (show 0≤(K+1)*diagonalControl Φ*(Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J)*Cscalar by positivity)
    convert hm using 1 <;> ring

end
end OAI.SevenEighths.Target830.Source.AssemblyComparison
#print axioms OAI.SevenEighths.Target830.Source.AssemblyComparison.actual_fixed_parent_comparison_fixed_mesh
end

/- Original module: Candidate.Target830.Source.Assembly.RawComparison. -/
section

namespace OAI.SevenEighths.Target830.Source.AssemblyComparison
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open Filter Cycle63Moment
open CenteredMomentPrimeSlot
open QuadraticInitialBound
open CenteredMomentEnergyReferenceState
open CenteredMomentEnergyState CenteredMomentEnergyReferenceChild
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentInductionEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

open OAI.SevenEighths.Cycle63FirstActual

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Literal original comparison energy at the common raw plain height. -/
theorem actual_fixed_parent_raw_comparison_fixed_mesh
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    0< comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (81/200)*M≤ n₁ → (81/200)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirst Z M)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hmesh,degree,S,hbound⟩ := actual_fixed_parent_comparison_fixed_mesh rayM H hH anchors
    Fmax Wslot aslot bslot lo hi haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε
    ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  refine ⟨hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*2^degree,by positivity,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ w σ freq
    t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hh := hz.2 j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ
    w σ freq t t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  have hX₁ : 0< comparisonFirst Z M := by unfold comparisonFirst; positivity
  have hX₂ : 0< comparisonSecond Z M (Z^n₁) (Z^n₂) := by
    unfold comparisonSecond comparisonFirst
    positivity
  have heq := actual_raw_radial_energy s rfl ha p
    (fun i:F => primePool rayM H bslot (Z^(w i)))
    (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i:F => Z^(w i)) (by intro i; positivity) t
    (comparisonFirst Z M) (comparisonSecond Z M (Z^n₁) (Z^n₂)) hX₁ hX₂
  have hbridge : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirst Z M)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*
      (1+|t|+|t|+height)^degree*Z^(M+ε) := by
    apply heq.trans_le
    convert hh using 1
    congr 1
    funext z
    rw [Finset.prod_coe_sort F (fun i => naturalSlot (naturalCharacter s.character z)
      (primePool rayM H bslot (Z^(w i)))
      (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))]
    ring
  apply hbridge.trans
  have hp : (1+|t|+|t|+height)^degree≤(2*(1+|t|+height))^degree :=
    pow_le_pow_left₀ (by positivity) (by linarith) degree
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hdom := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (show 0≤ C*diagonalControl Φ*(p.control S)^2 by positivity))
    (show 0≤ Z^(M+ε) by positivity)
  apply hdom.trans_eq
  rw [mul_pow]
  ring

end
end OAI.SevenEighths.Target830.Source.AssemblyComparison
#print axioms OAI.SevenEighths.Target830.Source.AssemblyComparison.actual_fixed_parent_raw_comparison_fixed_mesh
end
