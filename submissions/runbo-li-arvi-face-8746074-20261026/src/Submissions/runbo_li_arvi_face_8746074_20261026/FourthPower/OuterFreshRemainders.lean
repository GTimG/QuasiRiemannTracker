/- Copyright (c) 2026 Sil. Apache-2.0.
Actual outer-source zero and discarded terms. Both moving twists retain
their natural zeros; coefficient norms are derived from the true source.
K and W below use the common density convention. Original frequency k
is recovered by K=k/16, W=1, without any fourth-power transformation.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshAssembly
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedOriginalSecondZero
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedOriginalTailPower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshRemainders
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open RayFourExpansion CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSourceSecondZeroEnergy CenteredMomentFirstLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSourceInputTailUniform
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail MixedOriginalSecondZero MixedOriginalTailPower
open MixedPoissonLocalization MixedSupplierFourthRow MixedSupplierSource
open MixedInnerExceptionalLedger MixedLocalizedDictionary
open MixedSupplierOriginalFrequency OuterFreshRows OuterFreshWindowPair OuterFreshAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem outer_coefficient_norm (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (ξ : RayCharacter) (I : Id) :
    ‖outerColumn q x y seed ξ I‖≤‖sourceCoefficient s ha seed I‖ := by
  have he : outerColumn q x y seed ξ I=sourceCoefficient s ha seed I*
      (gate q x*twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ I) := by
    unfold outerColumn twist
    rw [common_coefficient q x s ha hm seed I]
    ring
  rw [he,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (factor_norm_le_one q x y ξ I)

theorem outer_coefficient_mass (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hb : 0≤b)
    (hm : Matches q x s ha) (seed : Id) (ξ : RayCharacter) :
    (∑I∈sourceColumns s,‖outerColumn q x y seed ξ I‖)≤massCap s :=
  (Finset.sum_le_sum (fun I _=>outer_coefficient_norm q x y s ha hm seed ξ I)).trans
    (original_coefficient_mass s ha hb seed)

/-- The actual diagonal, including the entire original artificial seed.
The conductor and both moving twists can only remove coefficient mass. -/
theorem outer_second_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀q : Data ι,
      ∀(x : Frozen q)(y : Selected q),∀a b : ℝ,∀s : Source (RestIndex q) a b,
      Fintype.card (RestIndex q)≤N → ∀ha : 0<a,Matches q x s ha →
      ∀(seed : Id)(ξ : RayCharacter)(τ : Character)(t Y : ℝ),seed≠0 → 1≤Y →
      sourceNormCap s.P b s.T s.d≤Y →
      ‖sourceSecondZero (sourceColumns s) (outerColumn q x y seed ξ) τ t‖≤
        C*(profileCap s)^2*Y^(1+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C0,hC0,hbound⟩ := original_column_bound N (ε/2) (half_pos hε)
  refine ⟨128*C0^2,by positivity,?_⟩
  intro ι instι q x y a b s hcard ha hm seed ξ τ t Y hseed hY hcap
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hs (I : Id) (hn : outerColumn q x y seed ξ I≠0) :=
    outer_coefficient_nonzero q x y s ha hm seed ξ I hn
  have hsize (I : Id) (hn : outerColumn q x y seed ξ I≠0) :=
    original_coefficient_cap s ha seed I (hs I hn)
  have hc (I : Id) (_hI : I∈supportedColumns (sourceColumns s))
      (hn : outerColumn q x y seed ξ I≠0) :
      ‖outerColumn q x y seed ξ I‖≤C0*profileCap s*Y^(ε/2) :=
    (outer_coefficient_norm q x y s ha hm seed ξ I).trans
      (hbound (RestIndex q) a b s hcard ha seed I Y (hsize I hn).1 hY
        ((hsize I hn).2.trans hcap))
  have hh := sourceSecondZero_divisor_bound (sourceColumns s) (outerColumn q x y seed ξ)
    τ t (C0*profileCap s*Y^(ε/2)) Y (by have := profileCap_nonneg s;positivity)
    hY0.le seed hseed hc (fun I _ hn=>source_coefficient_seed s ha seed I (hs I hn))
    (fun I _ hn=>(hsize I hn).2.trans hcap)
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  apply hh.trans_eq
  calc
    _=(128*C0^2)*(profileCap s)^2*((Y^(ε/2))^2*Y)/(seed.absNorm:ℝ) := by ring
    _=_ := by rw [hp]

/-- Literal outer Fourier tail, without a coefficient-mass hypothesis. -/
theorem outer_discarded_bound (Adec : ℕ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
      ∀(ι : Type u) [Fintype ι],∀q : Data ι,∀(x : Frozen q)(y : Selected q),
      ∀a b : ℝ,∀s : Source (RestIndex q) a b,∀ha : 0<a,0≤b → Matches q x s ha →
      ∀(seed : Id)(ξray : RayCharacter)(η : Character)(t K W X H Tsec Z Csec ξ : ℝ),
      0<K → 0<W → 0<X → 1<Z → 1≤Csec →
      sourceNormCap s.P b s.T s.d≤Real.exp H*X →
      X^2/(16*K*W^4)≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξray I*heightCoeff η t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖≤
      ((massCap s)^2*(16*K*W^4)*(Real.exp H*X)^2*
        (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec))/W := by
  obtain ⟨control,C,hC,htail⟩ := source_discarded_bound Adec
  refine ⟨control,C,hC,?_⟩
  intro ι instι q x y a b s ha hb hm seed ξray η t K W X H Tsec Z Csec ξ
    hK hW hX hZ hCs hcap hsec hthreshold
  have ht := htail η t (sourceColumns s) (outerColumn q x y seed ξray)
    K W X H Tsec Z Csec ξ hK hW hX hZ hCs
    (fun I _ hn=>((original_coefficient_cap s ha seed I
      (outer_coefficient_nonzero q x y s ha hm seed ξray I hn)).2).trans hcap) hsec hthreshold
  let F := (16*K*W^4)*(Real.exp H*X)^2*
    (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)/W
  have hF : 0≤F := by
    have := (show 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile from apply_nonneg _ _)
    have := zero_lt_one.trans hZ
    dsimp only [F]
    positivity
  have hmass := pow_le_pow_left₀
    (Finset.sum_nonneg (fun I _=>norm_nonneg (outerColumn q x y seed ξray I)))
    (outer_coefficient_mass q x y s ha hb hm seed ξray) 2
  apply ht.trans
  calc
    _=(∑I∈sourceColumns s,‖outerColumn q x y seed ξray I‖)^2*F := by dsimp only [F];ring
    _≤(massCap s)^2*F := mul_le_mul_of_nonneg_right hmass hF
    _=_ := by dsimp only [F];ring

/-- Arbitrary outer tail saving. The original-frequency specialization
K=k/16, W=1 meets the same numerical conditions, and uses no K4 gain. -/
theorem outer_tail_arbitrary_saving (B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀q : Data ι,∀(x : Frozen q)(y : Selected q),
      ∀a b : ℝ,∀s : Source (RestIndex q) a b,∀ha : 0<a,0≤b → Matches q x s ha →
      ∀(seed : Id)(ξray : RayCharacter)(η : Character)(t K W X Tsec : ℝ),0<K → 0<W → 0<X →
      poolCap s≤Z^B → sourceNormCap s.P b s.T s.d≤X →
      X≤Z^B → K≤Z^B → W≤Z^B → W⁻¹≤Z^B → Tsec≤Z^B → X^2/(16*K*W^4)≤Tsec →
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξray I*heightCoeff η t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖≤
      C*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving) := by
  obtain ⟨Adec,hdecay⟩ := choose_fourth_tail_order B ξ saving hB hξ
  obtain ⟨control,Ctail,hCtail,htail⟩ := outer_discarded_bound Adec
  refine ⟨control,64*Ctail,mul_pos (by norm_num) hCtail,?_⟩
  filter_upwards [eventually_tail_threshold 0 ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι q x y a b s ha hb hm seed ξray η t K W X Tsec hK hW hX
    hmass hcap hXc hKc hWc hWic hTc hscale
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) (by positivity : 0<16*K*W^4)).trans_le hscale
  have ht := htail ι q x y a b s ha hb hm seed ξray η t K W X 0 Tsec Z 1 ξ
    hK hW hX hZ.1 le_rfl (by simpa using hcap) hscale (by simpa using hZ.2)
  have hbnd := hdecay Z (poolCap s) K W X Tsec hZ.1.le (poolCap_nonneg s)
    hK hW hX hT hmass hKc hWc hXc hTc hWic
  have hp : 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
  have hfactor : 0≤Ctail*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile :=
    mul_nonneg (mul_nonneg hCtail.le (sq_nonneg _)) hp
  apply ht.trans
  calc
    _=(Ctail*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
        ((poolCap s)^2*(16*K*W^4)*X^2*((min 1 (kernelReference Tsec 0))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹/W) := by
      simp only [Real.exp_zero,one_mul,massCap,div_eq_mul_inv,mul_inv_rev,mul_pow]
      ring
    _≤(Ctail*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
        (64*Z^(-saving)) := mul_le_mul_of_nonneg_left hbnd hfactor
    _=_ := by ring

end
end Candidate.FourthPower.OuterFreshRemainders
