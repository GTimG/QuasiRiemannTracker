/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Generalized from Cycle61.Physical.FirstBranches.FixedComparison, source SHA256
576e3d7aff4f1bd817632e4c347999fa82ddc21e43c79b0277b25a58af52351b.
Underlying profile/scalar absorption: OpenAI/math, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.Reference
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.ReferenceEnvelope
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FirstBranches.FixedComparison

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalRowSource CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskEnergy
open Cycle61Moment Cycle61FirstGeometry Cycle61FirstActual Cycle61FirstReflection
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- A genuine uniform C28 short-factor/reference bound. The fixed incumbent,
actual ordinary reflection and common profile/scalar bounds discharge every
analytic term. Both exponents may be subunit; the long factor is split at M/2.
The full original fixed-parent mask and independent heights are preserved. -/
theorem actual_fixed_parent_short_reference
    (κ Kcap : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) (hKcap : 6*κ ≤ Kcap)
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0<a) (hlo : a≤1/4) (hhi : 1≤b)
    (hbΦ : 0<bΦ) (hMmin : 0<Mmin) (hMmax : Mmin≤Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    0<comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀j : Label, ∀M along short r cap : ℝ, Mmin≤M → M≤Mmax →
      0≤r → 0≤cap → short≤r → r+Kcap*cap≤49*M/100 →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀u t height : ℝ,
      (∀i,0≤w i) → (∀i,w i≤comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → (∑i∈F,w i)≤cap →
    ∀hZ : 1<Z, ∀hM : 0≤M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false (p.profile 1)
      (Z^along) 0 u * polynomial (naturalCharacter s.character z) false (p.profile 0) (Z^short) 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool rayM H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  have hMax : 0<Mmax := hMmin.trans_le hMmax
  let Mcap := 2*Mmax+1
  have hCap : 0<Mcap := by dsimp [Mcap]; positivity
  let d := comparisonD Mmax ε
  let xi := comparisonXi Mmin
  let L := comparisonL Mmin Mmax
  let saving := 2*Mcap+2*Mcap*d+1
  have hd : 0<d := by dsimp [d,comparisonD]; positivity
  have hxi : 0<xi := by dsimp [xi,comparisonXi]; positivity
  have hLpos : 0≤L := by dsimp [L,comparisonL]; positivity
  have hxirho : xi≤Mmin/100 := le_rfl
  have hL : Mcap+xi≤L := by dsimp [L,comparisonL,Mcap]; linarith
  have hmainReserve : d*(0+Mcap+2)≤ε/2 := by
    dsimp [d,comparisonD,Mcap]
    have hp : 0<4*(2*Mmax+1+2) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have herrReserve : 0*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε/2 := by
    dsimp [saving]
    nlinarith [mul_nonneg hCap.le hd.le]
  obtain ⟨Cscalar,hCs,hscalar⟩ := ledger_bound Mcap 0 bΦ L d saving (ε/2)
    hCap.le (by norm_num) hLpos hd hmainReserve herrReserve
  obtain ⟨degree,Sd,hterminal⟩ := Record12518109SourceLow.incumbent_at (α:=α)
    rayM H hH κ hκlo hκhi hκbeta Wslot aslot bslot a b bΦ 0 L lo hi Mcap d
    haslot hsSlot hWslot hbslot ha hlo hhi hbΦ (by norm_num) hCap hd hbeta
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,hCr,hDr,href⟩ :=
    reference_from_positive_with_error (α:=α) rayM H hH Fmax Wslot aslot bslot lo hi
      haslot hsSlot hWslot.continuous a b bΦ d xi (saving+Mcap) L
      ha hlo hhi hbΦ hd hxi 2 (by norm_num) degree Sd
  obtain ⟨J,S,Cprofile,hCp,hprofile⟩ := independent_reference_envelopes a b ha Sd T Slong
    degree n nlong Cref Dchild Dref hCr hDc hDr
  let delta := min 1 (ε/(2*Mmax))
  have hdelta : 0<delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta≤1 := min_le_left _ _
  have hdε : delta*Mmax≤ε/2 := by
    have hd' := min_le_right (1:ℝ) (ε/(2*Mmax))
    have hh := mul_le_mul_of_nonneg_right hd' hMax.le
    dsimp only [delta]
    field_simp at hh ⊢
    nlinarith
  refine ⟨comparisonMesh_pos Mmin Mmax ε hMmin hMmax hε, J,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kzero,K,hKzero,hK,ht⟩ := hterminal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cprofile*Cscalar*(K+1),by positivity,?_⟩
  filter_upwards [ht,href,fixed_anchor_width_uniform anchors Mmin delta hMmin hdelta]
    with Z hz hrefZ hanchor
  refine ⟨hz.1,?_⟩
  intro j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF θ w σ freq
    u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hwanchor := hanchor.2 j M hmin
  have hs : s.width≤Mcap := by
    have hh := mul_le_mul_of_nonneg_right hd1 hM
    change M+Real.logb Z ((anchors j).modulus.absNorm:ℝ)≤Mcap
    dsimp only [Mcap]; linarith only [hwanchor,hh,hmax]
  have hwidth : s.width≤M+ε/2 := by
    have hh := mul_le_mul_of_nonneg_left hmax hdelta.le
    change M+Real.logb Z ((anchors j).modulus.absNorm:ℝ)≤M+ε/2
    linarith only [hwanchor,hh,hdε]
  have hMw : M≤s.width := by
    change M≤M+s.characterWidth
    exact le_add_of_nonneg_right s.character_nonneg
  have hpad : xi≤M/100 := by linarith only [hxirho,hmin]
  have hκ : 0≤6*κ := by linarith only [hκlo]
  have hKone : 1≤Kcap := by linarith only [hκlo,hKcap]
  have hcapacityScalar : r+(6*κ)*cap≤49*M/100 := by
    have hk := mul_le_mul_of_nonneg_right hKcap hcap
    linarith only [hk,hbudget]
  have hrM : r≤Mcap := by
    have hk := mul_nonneg (zero_le_one.trans hKone) hcap
    linarith only [hbudget,hk,hM,hMw,hs]
  have hcapM : cap≤Mcap := by nlinarith only [hbudget,hr,hKone,hcap,hM,hMw,hs]
  have hshortM : short≤Mcap := hshort.trans hrM
  have hshortL : short≤L := by linarith only [hshortM,hL,hxi]
  have hp := hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) u t height hheight
  dsimp only at hp
  change _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J ∧
    _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J ∧
    _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J at hp
  let A := Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J
  let E := (K+1)*diagonalControl Φ*A
  have hdiag := diagonalControl_nonneg Φ
  have hA : 0≤A := by dsimp [A]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hKgrow : K*diagonalControl Φ*A≤E := by
    apply mul_le_mul_of_nonneg_right _ hA
    exact mul_le_mul_of_nonneg_right (by linarith only [hK]) hdiag
  have hdirect : K*diagonalControl Φ*
      ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).control Sd)^2*
      (1+|t|+height)^degree ≤ E := by
    apply le_trans _ hKgrow
    convert mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK.le hdiag) using 1 <;> ring
  have hmain : Cref*(sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
      (K*diagonalControl Φ*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|+height)^(degree+2*n))≤E := by
    apply le_trans _ hKgrow
    convert mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK.le hdiag) using 1 <;> ring
  have herr : Dref*(sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl Φ≤E := by
    have hk : diagonalControl Φ*A≤E := by
      calc
        _ = 1*diagonalControl Φ*A := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hK]) hdiag) hA
    apply le_trans _ hk
    convert mul_le_mul_of_nonneg_left hp.2.2 hdiag using 1 <;> ring
  have hsum : (∑i : F,w i)≤Mcap := by rw [Finset.sum_coe_sort]; exact hslots.trans hcapM
  have hledger := hscalar Z hZ.le s hs F (fun i => w i) hsum
  have hrad : (s.puncture.radical.absNorm:ℝ)^d=1 := by
    change (((1:Ideal O).radical).absNorm:ℝ)^d=1
    simp [Ideal.radical_top,Ideal.absNorm_top]
  rw [hrad,one_mul] at hledger
  rw [Finset.prod_coe_sort F (fun i => Z^(w i))] at hledger
  have hlog : 0≤Real.log Z := (Real.log_pos hZ).le
  let P := Z^(s.width+d)
  let Qmain := (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
    (1+2*(L*Real.log Z))*P
  let Qerror := (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i∈F,Z^(w i))
  have hP : 0≤P := by dsimp [P]; positivity
  have hQm : 0≤Qmain := by dsimp [Qmain]; positivity
  have hQe : 0≤Qerror := by dsimp [Qerror]; positivity
  have hbounded : radialEnergy (fun z =>
      polynomial (naturalCharacter s.character z) false (p.profile 1) (Z^along) 0 u *
      polynomial (naturalCharacter s.character z) false (p.profile 0) (Z^short) 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool rayM H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep Φ (Z^M) ≤ E*(P+Qmain+Qerror) := by
    by_cases hlong : along≤M/2
    · have hc := direct_short_capacity Z M s.width short along (∑i∈F,w i)
        r cap (6*κ) hZ hM hMw hr hκ hshort hslots hcapacityScalar hlong
      have hl : along≤L := by linarith only [hlong,hM,hMw,hs,hxi,hL]
      have he := Cycle61FirstDirect.direct_child_from_positive rayM H hH Wslot bslot a b bΦ
        0 L (comparisonMesh Mmin Mmax ε) lo hi Mcap d κ Z η₀ Q
        degree Sd K hz.2.2 (by norm_num) ha F θ w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq
        s rfl hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) (Z^along) (Z^short)
        (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
        (Real.rpow_le_rpow_of_exponent_le hZ.le hl)
        (Real.rpow_le_rpow_of_exponent_le hZ.le hshortL) hc
      apply he.trans
      apply (mul_le_mul_of_nonneg_right hdirect hP).trans
      apply mul_le_mul_of_nonneg_left _ hE
      linarith only [hQm,hQe]
    · have hlong' : M/2≤along := le_of_not_ge hlong
      have hlength : s.width≤L+along := by linarith only [hs,hL,hlong',hM,hxi]
      have hwindow : max 0 (s.width-along+xi)≤L := max_le hLpos (by linarith only [hs,hL,hlong',hM])
      have hc := clipped_short_capacity Z M s.width short along (∑i∈F,w i)
        r cap (6*κ) xi hZ hM hMw hr hcap hκ hshort hslots hcapacityScalar hlong' hxi.le hpad
      have he := hrefZ.2 0 L (comparisonMesh Mmin Mmax ε) Mcap d κ η₀ Q K hK.le hz.2.2
        (by norm_num) F hF θ w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq
        s rfl hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
        along short hlength hwindow hshortL hc
      dsimp only at he
      have hdecay := decay_short_le Z saving Mcap s.width short hZ.le hCap.le s.width_nonneg hshortM
      have htMain := mul_le_mul_of_nonneg_right hmain hQm
      have htError := mul_le_mul_of_nonneg_right herr hQe
      have ht : E*Qmain+E*Qerror≤E*(P+Qmain+Qerror) := by nlinarith only [mul_nonneg hE hP]
      apply he.trans
      apply le_trans _ ((add_le_add htMain htError).trans ht)
      apply add_le_add
      · dsimp [Qmain,P]
        calc
          _ ≤ Cref*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
            (sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
            (1+2*(L*Real.log Z))*
            (K*diagonalControl Φ*Dchild*(sourceControl T (p.profile 0))^2*
              (1+|t|+height)^(degree+2*n)*Z^(s.width+d)) := by gcongr <;> rfl
          _ = _ := by simp only [Real.norm_eq_abs,schwartzSeminormFamily]; ring
      · dsimp [Qerror]
        have hnonneg : 0≤Dref*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          (sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
          diagonalControl Φ*max 1 s.radial.scale*(∏i∈F,Z^(w i)) := by positivity
        convert mul_le_mul_of_nonneg_left hdecay hnonneg using 1 <;>
          simp only [show s.radial.profile = Φ from rfl, Real.norm_eq_abs,schwartzSeminormFamily] <;> ring
  apply hbounded.trans
  have hlast := mul_le_mul_of_nonneg_left hledger hE
  apply hlast.trans
  dsimp [E,A]
  have hzpow := Real.rpow_le_rpow_of_exponent_le hZ.le (show s.width+ε/2≤M+ε by linarith only [hwidth])
  have hm := mul_le_mul_of_nonneg_left hzpow
    (show 0≤(K+1)*diagonalControl Φ*(Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J)*Cscalar by positivity)
  convert hm using 1 <;> ring

end
end OAI.SevenEighths.Record1252270103Low
#print axioms OAI.SevenEighths.Record1252270103Low.actual_fixed_parent_short_reference
