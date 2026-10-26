import Candidate.Cycle63.Physical.FirstBranches.RawComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
import Candidate.Cycle63.Moment.InitialAffineContract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import Candidate.Cycle63.Physical.SecondZero.Uniform
import Candidate.Cycle63.Physical.ClippedProjectorShell

/- Original module: Candidate.Cycle63.Physical.InitialSourceReduction. -/
section

namespace OAI.SevenEighths.Cycle63InitialSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentFirstSourceReduction
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentSourceInputTailUniform CenteredMomentNaturalFixedRaySource
open Cycle63Moment Cycle63FirstActual CenteredMomentEnergyOriginalProfileControl
open CenteredMomentPrimeSlot CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Actual equal-product source at the physical row width M, rather than the
larger conductor width recorded by NaturalState. -/
def affineInput (η₀ : Character) (θ : ι→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ) (haslot : 0<aslot)
    (hWs : Function.support W⊆Set.Icc aslot bslot)
    (w σ v : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc lo hi)
    {Z bΦ a b : ℝ} (s : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0<a)
    (M t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) : Input ι :=
  CenteredMomentEnergyNaturalInputMatches.input rayM H hH η₀ θ W hW aslot bslot lo hi
    haslot hWs w σ v hσ s p ha t X₁ X₂
    (comparisonFirst Z M) (comparisonSecond Z M X₁ X₂) hX₁ hX₂
    (comparison_positive Z M X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z M X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z M X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

omit [DecidableEq ι] in
lemma affine_volume_bound (Z M Mmax X₁ X₂ : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hM : 0≤M) (hmax : M≤Mmax) (_hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hn₁ : length Z X₁≤(44/100)*M) (hn₂ : length Z X₂≤(44/100)*M)
    (hslots : (∑i,w i)≤M/25) : X₁*X₂*(∏i,Z^(w i))≤Z^(Mmax+1) := by
  have hz := zero_lt_one.trans hZ
  have hx (X : ℝ) : X≤Z^(length Z X) := by
    rw [length,Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _ ≤ Z^(length Z X₁)*Z^(length Z X₂)*(∏i,Z^(w i)) := by
      gcongr
      · exact hx X₁
      · exact hx X₂
    _ = Z^(length Z X₁+length Z X₂+∑i,w i) := by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

lemma fixed_inverse_scale_bound (Z M Mmax : ℝ) (hZ : 1<Z) (hM : 0≤M)
    (hmax : M≤Mmax) : (Z^M)⁻¹≤Z^(Mmax+1) := by
  have hZpow := Real.one_le_rpow hZ.le hM
  have hinv : (Z^M)⁻¹≤1 := inv_le_one_of_one_le₀ hZpow
  exact hinv.trans (Real.one_le_rpow hZ.le (by linarith))

lemma initial_scale_exact (Z X M : ℝ) (hZ : 1<Z) (hM : 0<M)
    (hlo : (41/100)*M≤length Z X) : X=Z^(length Z X) := by
  have hx : 1<X := by
    by_contra h
    have he : length Z X=0 := by simp only [length,max_eq_left (le_of_not_gt h),Real.logb_one]
    linarith
  rw [length,max_eq_right hx.le,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans hx)]

/-- One actual radial majorant and remainder constant work for every live finite
slot subset. Fixed Ψ seminorms are absorbed before any live input is chosen. -/
theorem uniform_original_reduction {α : Type*} [Fintype α] [DecidableEq α]
    (bΦ bslot a b B ε ξ saving : ℝ)
    (hbΦ : 0<bΦ) (hbslot : 0≤bslot) (ha : 0<a) (hb : 0≤b)
    (hB : 0≤B) (hε : 0<ε) (hξ : 0<ξ) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃D : ℝ, 0<D ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀T : Finset α, ∀inp : Input T, ∀p : Profiles a b,
      inp.W₁=p.profile 0 → inp.W₂=p.profile 1 → (∀i,inp.hi i≤bslot) →
    ∀R : Ideal O, ∀r : CenteredMomentRadialEligibleEnergy.Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume inp≤Z^B → r.scale⁻¹≤Z^B →
    energy inp.η (fixedBadMask*idealGenerator R) 1 inp.t inp.W₁ inp.W₂ inp.slots
      inp.toData.coefficient inp.P inp.X₁ inp.X₂ r.keep r.profile r.scale ≤
      2*diagonalControl r.profile*(
        physicalMass inp R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        D*(plainControl inp (p.profile 0) (p.profile 1))^2*r.scale*(Z^ε+Z^(-saving)))+
      2*energy inp.η (fixedBadMask*idealGenerator R) 1 inp.t inp.W₁ inp.W₂ inp.slots
        inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ r.keep r.profile r.scale := by
  obtain ⟨Ψ,hΨ,hΨpos,hmajor⟩ := CenteredMomentEnergyFixedRadialSource.fixed_source bΦ hbΦ
  have hred (T : Finset α) := original_first_physical_reduction (ι:=T)
    (fun _ => bslot) a b B ε ξ saving (fun _ => hbslot) ha hb hB hε hξ
  choose Sd St Cd Ct hCd hCt hred using hred
  let D := 1+∑T : Finset α,(Cd T*sourceControl (Sd T) Ψ+Ct T*sourceControl (St T) Ψ)
  have hterms (T : Finset α) : 0≤Cd T*sourceControl (Sd T) Ψ+Ct T*sourceControl (St T) Ψ := by
    exact add_nonneg (mul_nonneg (hCd T).le (sourceControl_nonneg _ _))
      (mul_nonneg (hCt T).le (sourceControl_nonneg _ _))
  have hD : 0<D := by
    have hh := Finset.sum_nonneg (s:=Finset.univ) (fun T _ => hterms T)
    dsimp [D]; linarith
  refine ⟨Ψ,hΨ,hΨpos,D,hD,?_⟩
  filter_upwards [eventually_all.mpr hred,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro T inp p he₁ he₂ hhi R r hr hV hKi
  let : DecidableEq (T⊕Fin 2) := energyOriginalSourceDecidableSum
  have hh := (hz T).2 inp (p.profile 0) (p.profile 1) he₁ he₂ (p.support 0) (p.support 1)
    hhi fixedBadMask 1 (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 Ψ r.scale r.scale_pos hV hKi
  have hdom := hmajor r.profile hr inp.η fixedBadMask 1 inp.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset inp.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient inp R 1) r.scale r.scale_pos
  have hd := diagonalControl_nonneg r.profile
  have hcmp := positive_energy_comparison inp R r
  have hsum := Finset.single_le_sum (fun T _ => hterms T) (Finset.mem_univ T)
  have hCdD : Cd T*sourceControl (Sd T) Ψ≤D := by
    dsimp [D]
    linarith [mul_nonneg (hCt T).le (sourceControl_nonneg (St T) Ψ)]
  have hCtD : Ct T*sourceControl (St T) Ψ≤D := by
    dsimp [D]
    linarith [mul_nonneg (hCd T).le (sourceControl_nonneg (Sd T) Ψ)]
  have hbound := div_le_div_of_nonneg_right hdom
    (CenteredMomentAmplificationChildInput.volume_pos inp).le
  have hbound' := mul_le_mul_of_nonneg_left hh hd
  rw [mul_div_assoc] at hbound
  change _ ≤ diagonalControl r.profile * _ at hbound'
  apply hcmp.trans
  apply add_le_add _ le_rfl
  have hf := mul_le_mul_of_nonneg_left (hbound.trans hbound') (show (0:ℝ)≤2 by norm_num)
  simp only [mul_div_assoc]
  apply hf.trans
  have hscale := r.scale_pos
  have hZpos := zero_lt_one.trans hZ
  dsimp only [sourceControl] at hCdD hCtD
  have he : _ ≤ _ := add_le_add
    (mul_le_mul_of_nonneg_right hCdD (show 0≤(plainControl inp (p.profile 0) (p.profile 1))^2*r.scale*Z^ε by positivity))
    (mul_le_mul_of_nonneg_right hCtD (show 0≤(plainControl inp (p.profile 0) (p.profile 1))^2*r.scale*Z^(-saving) by positivity))
  have he' := mul_le_mul_of_nonneg_left (add_le_add_left he
    (physicalMass inp R 1 fixedBadMask 1 Ψ r.scale Z ξ/CenteredMomentAmplificationChildInput.volume inp))
    (show 0≤2*diagonalControl r.profile by positivity)
  simp only [CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume] at he' ⊢
  convert he' using 1 <;> ring

/-- Extend live slot data only to use a fixed finite ambient dictionary. -/
def slotExtend {α : Type*} [DecidableEq α] {γ : Type*}
    (T : Finset α) (f : T→γ) (fallback : γ) (i : α) : γ :=
  if h : i∈T then f ⟨i,h⟩ else fallback

@[simp] lemma slotExtend_coe {α : Type*} [DecidableEq α] {γ : Type*}
    (T : Finset α) (f : T→γ) (fallback : γ) (i : T) :
    slotExtend T f fallback i=f i := by simp [slotExtend,i.property]

private lemma control_insert {a b : ℝ} (p : Profiles a b) (S : Finset (ℕ×ℕ)) :
    p.control S≤p.control (insert (0,0) S) := by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

/-- Actual initial affine energy reduced to its actual normalized physical mass.
All other terms are proved from the literal .41--.44 initial scales and the
original daughter terminal; no parent-capacity input is used. -/
theorem actual_initial_source_reduction_fixed_mesh {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (anchors : Label→Character)
    (W : ℝ→ℂ) (aslot bslot lo hi a b bΦ Mmin Mmax ε ξ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (hlohi : lo≤hi)
    (ha : 0<a) (hlo : a≤1/4) (hhi : 1≤b) (hbΦ : 0<bΦ)
    (hMmin : 0<Mmin) (hMmax : Mmin≤Mmax) (hε : 0<ε) (hξ : 0<ξ)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ 0<comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀j : Label, ∀T : Finset α, ∀θ : T→RayQuotient.Characters rayM H,
    ∀w σ freq : T→ℝ, ∀t height : ℝ,
      (∀i,0≤w i) → (∀i,w i≤comparisonMesh Mmin Mmax ε) → ∀hσlo : (∀i,lo≤σ i), ∀hσhi : (∀i,σ i≤hi),
      0≤height → (∀i,|freq i|≤height) →
    ∀M : ℝ, Mmin≤M → M≤Mmax →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b, ∀X₁ X₂ : ℝ,
    ∀hX₁ : 0<X₁, ∀hX₂ : 0<X₂,
      (41/100)*M≤length Z X₁ → length Z X₁≤(44/100)*M →
      (41/100)*M≤length Z X₂ → length Z X₂≤(44/100)*M →
      (∑i,w i)≤M/25 → ∀hZ : 1<Z, ∀hM : 0≤M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha M t X₁ X₂ hX₁ hX₂;
    energy (anchors j) (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp)+
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  have hMax : 0<Mmax := hMmin.trans_le hMmax
  obtain ⟨Ψ,hΨ,hΨpos,D,hD,hred⟩ := uniform_original_reduction (α:=α)
    bΦ bslot a b (Mmax+1) (ε/2) ξ 1 hbΦ hbslot ha (by linarith)
    (by linarith) (by positivity) hξ
  obtain ⟨hmesh,degree,S,hcomp⟩ := actual_fixed_parent_raw_comparison_fixed_mesh rayM H hH anchors
    (Finset.univ:Finset α) W aslot bslot lo hi haslot hWs hW hbslot
    a b bΦ Mmin Mmax ε ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  let mesh := comparisonMesh Mmin Mmax ε
  let G := (CenteredMomentEnergyNaturalInputMatches.profileBound W hW.continuous
    aslot bslot lo hi haslot hWs)^(2*Fintype.card α)
  have hG : 0≤G := pow_nonneg (zero_le_one.trans
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW.continuous
      aslot bslot lo hi haslot hWs)) _
  refine ⟨Ψ,hΨ,hΨpos,hmesh,degree,insert (0,0) S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hcomp η₀ Q hQM hQ0 hQt hQ72
  refine ⟨4*D*G+2*C,by positivity,?_⟩
  filter_upwards [ht,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro j T θ w σ freq t height hw hwmesh hσlo hσhi hheight hfreq M hmin hmax
    Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hn₁ hn₁' hn₂ hn₂' hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha M t X₁ X₂ hX₁ hX₂
  have hv : CenteredMomentAmplificationChildInput.volume inp≤Z^(Mmax+1) :=
    affine_volume_bound Z M Mmax X₁ X₂ w hZ hM hmax hX₁ hX₂ hn₁' hn₂' hslots
  have hred' := hr.2 T inp p rfl rfl (fun _=>le_rfl) 1 s.radial hsΦ hv
    (fixed_inverse_scale_bound Z M Mmax hZ hM hmax)
  have hn₁eq := initial_scale_exact Z X₁ M hZ (hMmin.trans_le hmin) hn₁
  have hn₂eq := initial_scale_exact Z X₂ M hZ (hMmin.trans_le hmin) hn₂
  let we := slotExtend T w 0
  let se := slotExtend T σ lo
  let ve := slotExtend T freq 0
  have hew (i : α) : 0≤we i := by
    dsimp [we,slotExtend]; split_ifs with h
    · exact hw ⟨i,h⟩
    · exact le_rfl
  have hewm (i : α) : we i≤mesh := by
    dsimp [we,slotExtend]; split_ifs with h
    · exact hwmesh ⟨i,h⟩
    · exact hmesh.le
  have heslo (i : α) : lo≤se i := by
    dsimp [se,slotExtend]; split_ifs with h
    · exact hσlo ⟨i,h⟩
    · exact le_rfl
  have heshi (i : α) : se i≤hi := by
    dsimp [se,slotExtend]; split_ifs with h
    · exact hσhi ⟨i,h⟩
    · exact hlohi
  have hev (i : α) : |ve i|≤height := by
    dsimp [ve,slotExtend]; split_ifs with h
    · exact hfreq ⟨i,h⟩
    · simpa only [abs_zero] using hheight
  have hesum : (∑i∈T,we i)≤M/25 := by
    rw [←Finset.sum_coe_sort T we]
    simpa only [we,slotExtend_coe] using hslots
  have hc := hz.2 j M (length Z X₁) (length Z X₂) hmin hmax hn₁ hn₂ hn₁' hn₂'
    Φ hsΦ hpΦ p T (Finset.subset_univ _) (slotExtend T θ 1) we se ve t height
    hew hewm heslo heshi hheight hev hesum hZ hM
  simp only [we,se,ve,slotExtend_coe,←hn₁eq,←hn₂eq] at hc
  have hplain : (plainControl inp (p.profile 0) (p.profile 1))^2≤
      G*(p.control (insert (0,0) S))^2 := plain_control_sq_le inp p S (Fintype.card α) _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW.continuous
      aslot bslot lo hi haslot hWs)
    (by simpa using Finset.card_le_univ T) (fun _=>le_rfl)
  have hpc := pow_le_pow_left₀ (p.control_nonneg S) (control_insert p S) 2
  have hdiag := diagonalControl_nonneg Φ
  have hheight1 : 1≤(1+|t|+height)^degree := one_le_pow₀ (by linarith [abs_nonneg t])
  have hpowers : (Z^M)*(Z^(ε/2)+Z^(-(1:ℝ)))≤2*Z^(M+ε) := by
    have hterm (e : ℝ) (he : e≤ε) : Z^M*Z^e≤Z^(M+ε) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    nlinarith [hterm (ε/2) (by linarith),hterm (-1) (by linarith)]
  have hrem : 2*diagonalControl Φ*(D*(plainControl inp (p.profile 0) (p.profile 1))^2*
      (Z^M)*(Z^(ε/2)+Z^(-(1:ℝ))))≤
      4*D*G*diagonalControl Φ*(p.control (insert (0,0) S))^2*
        (1+|t|+height)^degree*Z^(M+ε) := by
    calc
      _ ≤ 2*diagonalControl Φ*(D*(G*(p.control (insert (0,0) S))^2)*
          (2*Z^(M+ε))) := by
        have hh := mul_le_mul (mul_le_mul_of_nonneg_left hplain hD.le) hpowers
          (show 0≤Z^M*(Z^(ε/2)+Z^(-(1:ℝ))) by positivity)
          (show 0≤D*(G*(p.control (insert (0,0) S))^2) by positivity)
        have hh' := mul_le_mul_of_nonneg_left hh
          (show 0≤2*diagonalControl Φ from mul_nonneg (by norm_num) hdiag)
        convert hh' using 1; ring
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right
          (show 0≤4*D*G*diagonalControl Φ*(p.control (insert (0,0) S))^2*Z^(M+ε) by positivity) hheight1
        convert hh using 1 <;> ring
  have hc' := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)
  have hcomparison : 2*energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ s.radial.keep Φ (Z^M)≤
      2*C*diagonalControl Φ*(p.control (insert (0,0) S))^2*
        (1+|t|+height)^degree*Z^(M+ε) := by
    apply hc'.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpc (mul_nonneg hC.le hdiag))
        (show 0≤(1+|t|+height)^degree by positivity))
      (show 0≤Z^(M+ε) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤2 by norm_num)
    convert hh' using 1; ring
  change _ ≤ 2*diagonalControl Φ*(
      physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp+
      D*(plainControl inp (p.profile 0) (p.profile 1))^2*(Z^M)*(Z^(ε/2)+Z^(-(1:ℝ))))+
    2*energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots
      inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ s.radial.keep Φ (Z^M) at hred'
  apply hred'.trans
  change 2*diagonalControl Φ*(_+_)+_≤_
  rw [mul_add]
  have hh := add_le_add_left (add_le_add hrem hcomparison)
    (2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
      CenteredMomentAmplificationChildInput.volume inp))
  convert hh using 1 <;> ring

theorem actual_initial_source_reduction {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (anchors : Label→Character)
    (W : ℝ→ℂ) (aslot bslot lo hi a b bΦ Mmin Mmax ε ξ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (hlohi : lo≤hi)
    (ha : 0<a) (hlo : a≤1/4) (hhi : 1≤b) (hbΦ : 0<bΦ)
    (hMmin : 0<Mmin) (hMmax : Mmin≤Mmax) (hε : 0<ε) (hξ : 0<ξ)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃mesh : ℝ, 0<mesh ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀j : Label, ∀T : Finset α, ∀θ : T→RayQuotient.Characters rayM H,
    ∀w σ freq : T→ℝ, ∀t height : ℝ,
      (∀i,0≤w i) → (∀i,w i≤mesh) → ∀hσlo : (∀i,lo≤σ i), ∀hσhi : (∀i,σ i≤hi),
      0≤height → (∀i,|freq i|≤height) →
    ∀M : ℝ, Mmin≤M → M≤Mmax →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b, ∀X₁ X₂ : ℝ,
    ∀hX₁ : 0<X₁, ∀hX₂ : 0<X₂,
      (41/100)*M≤length Z X₁ → length Z X₁≤(44/100)*M →
      (41/100)*M≤length Z X₂ → length Z X₂≤(44/100)*M →
      (∑i,w i)≤M/25 → ∀hZ : 1<Z, ∀hM : 0≤M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha M t X₁ X₂ hX₁ hX₂;
    energy (anchors j) (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp)+
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨Ψ,hs,hp,hm,J,S,hbound⟩ := actual_initial_source_reduction_fixed_mesh (α:=α)
    rayM H hH anchors W aslot bslot lo hi a b bΦ Mmin Mmax ε ξ haslot hWs hW hbslot
    hlohi ha hlo hhi hbΦ hMmin hMmax hε hξ hbeta hκbeta
  exact ⟨Ψ,hs,hp,comparisonMesh Mmin Mmax ε,hm,J,S,hbound⟩

end
end OAI.SevenEighths.Cycle63InitialSource
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.SourceCaps. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentAmplificationChildSourceCaps Cycle63InitialSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

section Literal
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂

theorem affine_literal_fields :
    (∀ i, (inp).M i = CenteredMomentEnergyNaturalInputMatches.profileBound
      W hW aslot bslot lo hi haslot hWs) ∧
    (inp).upper = bslot ∧ (∀ i, (inp).hi i = bslot) ∧
    (inp).b₁ = b ∧ (inp).b₂ = b ∧ (inp).W₁ = p.profile 0 ∧ (inp).W₂ = p.profile 1 ∧
    (∀ i, (inp).P i = Z^(w i)) ∧ (inp).η = state.character ∧ (inp).m = state.mask ∧
    (inp).t = t ∧
    CenteredMomentAllocatedRayDictionary.Matches rayM H hH inp η₀ θ w σ freq W bslot Z := by
  refine ⟨fun _ => rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, rfl, rfl, rfl, ?_⟩
  constructor <;> intros <;> rfl

theorem affine_endpoints (hbslot : 0 ≤ bslot) (hb : 0 ≤ b) :
    Endpoints (max 1 bslot) b b inp := by
  exact ⟨le_max_right _ _, fun _ => hbslot, hb, le_rfl, hb, le_rfl⟩

/-- The comparison rectangle is bounded from its actual equal-product formula. -/
theorem affine_plain_caps (Mmax : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M) (hmax : M ≤ Mmax)
    (hn₁ : length Z X₁ ≤ (44/100)*M) (hn₂ : length Z X₂ ≤ (44/100)*M) :
    ∀ second j, Cycle63.Physical.sourcePlainScales (inp).toData.toSource second j ≤ Z^Mmax := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hx (X : ℝ) : X ≤ Z^(length Z X) := by
    rw [length, Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hx₁ : X₁ ≤ Z^((44/100)*M) := (hx X₁).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hn₁)
  have hx₂ : X₂ ≤ Z^((44/100)*M) := (hx X₂).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hn₂)
  have hfirst : comparisonFirst Z M ≤ Z^Mmax := by
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hprod : X₁*X₂ ≤ Z^((44/100)*M+(44/100)*M) := by
    rw [Real.rpow_add hz]
    exact mul_le_mul hx₁ hx₂ hX₂.le (Real.rpow_nonneg hz.le _)
  have hsecond : comparisonSecond Z M X₁ X₂ ≤ Z^Mmax := by
    unfold comparisonSecond comparisonFirst
    calc
      _ ≤ Z^((44/100)*M+(44/100)*M)/Z^(M/4) :=
        div_le_div_of_nonneg_right hprod (Real.rpow_nonneg hz.le _)
      _ = Z^((44/100)*M+(44/100)*M-M/4) := (Real.rpow_sub hz _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have h₁ : X₁ ≤ Z^Mmax := hx₁.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have h₂ : X₂ ≤ Z^Mmax := hx₂.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  intro second j
  cases second <;> fin_cases j
  · exact h₁
  · exact h₂
  · exact hfirst
  · exact hsecond
end Literal

/-- The fixed caps precede every live slot subset and all source parameters. -/
theorem fixed_affine_source_caps {α : Type*} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi a b : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hbslot : 0 ≤ bslot) (ha : 0 < a) (hb : 1 ≤ b) :
    ∃ Cs bs bp : ℝ, 1 ≤ Cs ∧ 1 ≤ bs ∧ 1 ≤ bp ∧
    ∀ (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
      {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b)
      (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
    let inp := affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂
    Fintype.card T ≤ Fintype.card α ∧ (∀ i, (inp).M i ≤ Cs) ∧ (inp).upper ≤ bs ∧
    Endpoints bs bp bp inp ∧ (inp).b₁ = bp ∧ (inp).b₂ = bp ∧
    (inp).W₁ = p.profile 0 ∧ (inp).W₂ = p.profile 1 ∧ (inp).η = state.character ∧
    CenteredMomentAllocatedRayDictionary.Matches rayM H hH inp η₀ θ w σ freq W bslot Z := by
  let Cs := CenteredMomentEnergyNaturalInputMatches.profileBound
    W hW aslot bslot lo hi haslot hWs
  refine ⟨Cs, max 1 bslot, b,
    CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one
      W hW aslot bslot lo hi haslot hWs, le_max_left _ _, hb, ?_⟩
  intro T η₀ θ w σ freq hσ Z bΦ state p M t X₁ X₂ hX₁ hX₂
  refine ⟨Fintype.card_le_of_injective (fun i : T => i.val) Subtype.val_injective,
    fun _ => le_rfl, le_max_right _ _, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · exact affine_endpoints rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ hbslot (zero_le_one.trans hb)
  · constructor <;> intros <;> rfl

#print axioms affine_literal_fields
#print axioms affine_endpoints
#print axioms affine_plain_caps
#print axioms fixed_affine_source_caps
end
end OAI.SevenEighths.Cycle63InitialMass
end
