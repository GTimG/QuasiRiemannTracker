/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryTailChild
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorSecondSplit
import Candidate.Cycle63.Physical.InitialMass.GeometryTailPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentSupportedTailAggregate CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements RayFourExpansion ConcretePrimeRowBridge CenteredMomentFirstAnnularInput
local instance errorTailDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Constants are chosen over the finite original slot dictionary before
both allocations, both characters, and both independent heights. -/
theorem actual_twice_child_second_tail {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B ξ saving : ℝ)(hCs : 1≤Cs)(hb : 0≤b)
    (hlo : 0<lo)(hhi : 0≤hi)(hB : 0≤B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input α),Fintype.card α≤N → (∀i,s.M i≤Cs) → (∀i,s.hi i≤b) →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(C R seed : Ideal O)(B₁ : actualAllocations s.pools C)(χ : Character)(t : ℝ)
      (Q : Ideal O)(k : ℕ)
      (Bp : actualAllocations (child s C R B₁ χ t).pools (Q^k))
      (υ : Character)(v : ℝ)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),0<K →
    let u := twiceChild s C R B₁ χ t Q k Bp υ v
    volume u≤Z^B → Tsec≤Z^B → (volume u)^2/K≤Tsec →
    ‖secondDiscardedEnergy u.η u.t (original u ((R*C)*(Q^k)) seed).columns
      (original u ((R*C)*(Q^k)) seed).beta Φ K Tsec Z ξ‖/volume u≤
      Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  have hex (J : Finset α) := actual_common_child_second_tail (α:=J)
    N Cs b lo hi B ξ saving hCs hb hlo hhi hB hξ
  choose F D hD hbound using hex
  let F₀ := Finset.univ.biUnion F
  let C₀ := ∑J : Finset α,D J
  refine ⟨F₀,C₀,Finset.sum_pos (fun J _=>hD J) Finset.univ_nonempty,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  refine ⟨(hz ∅).1,?_⟩
  intro s hn hm hs p hp₁ hp₂ C R seed B₁ χ t Q k Bp υ v Φ K Tsec hK u hV hT hnom
  have hh := (hz (liveIndices B₁.val)).2 (child s C R B₁ χ t)
    ((live_card_le B₁.val).trans hn) (fun i=>hm i.val) (fun i=>hs i.val) p hp₁ hp₂
    (Q^k) (R*C) seed Bp υ v Φ K Tsec hK hV hT hnom
  have hCJ : D (liveIndices B₁.val)≤C₀ := Finset.single_le_sum
    (fun J _=>(hD J).le) (Finset.mem_univ _)
  have hF := (Finset.sup_mono
    (Finset.subset_biUnion_of_mem F (Finset.mem_univ (liveIndices B₁.val))) :
    (F (liveIndices B₁.val)).sup (schwartzSeminormFamily ℝ ℝ ℂ)≤F₀.sup (schwartzSeminormFamily ℝ ℝ ℂ)) Φ
  have hzpos : 0<Z := zero_lt_one.trans (hz ∅).1
  have hC₀ : 0<C₀ := Finset.sum_pos (fun J _=>hD J) Finset.univ_nonempty
  apply hh.trans
  gcongr

/-- The literal error radius stays in a polynomial box. The hypothesis
on the prime is only its genuine nonzero ideal norm. -/
theorem actual_error_radius_box (reflected : Bool)(C D E : Ideal O)
    (hC : C≠0)(hD : D≠0)(hE : E≠0)
    (heq : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (Z M V a δ reserve B : ℝ)(hZ : 1<Z)(hV : 0<V)(hB : 0≤B)
    (hM : 0≤M)(hMB : M≤B)(ha : 0≤a)(haB : a≤B)(hδ : 0≤δ)(hr : 0≤ reserve)
    (hω : δ+reserve≤B)(hA : |Real.logb Z V|≤B)
    (hc : Real.logb Z (C.absNorm:ℝ)≤B)(hd : Real.logb Z (D.absNorm:ℝ)≤B)
    (he : Real.logb Z (E.absNorm:ℝ)≤B)
    (hactive : Real.logb Z (Ideal.span {activeConductor C D}).absNorm≤B)
    (q : O)(hq : q≠0)(k : ℕ)(hk : 1≤k) :
    Z^(-5*B)≤errorCommonRadius Z (Real.logb Z ((if reflected then C else D).absNorm:ℝ))
      (nominalLog C D E (Z^M) V Z) (Real.logb Z ((if reflected then D else C).absNorm:ℝ))
      (3*a) δ reserve q k ∧
    errorCommonRadius Z (Real.logb Z ((if reflected then C else D).absNorm:ℝ))
      (nominalLog C D E (Z^M) V Z) (Real.logb Z ((if reflected then D else C).absNorm:ℝ))
      (3*a) δ reserve q k≤Z^(12*B) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc0 := Real.logb_nonneg hZ (norm_ge_one C hC)
  have hd0 := Real.logb_nonneg hZ (norm_ge_one D hD)
  have he0 := Real.logb_nonneg hZ (norm_ge_one E hE)
  have hr0 : 0≤Real.logb Z (Ideal.span {activeConductor C D}).absNorm :=
    Real.logb_nonneg hZ (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr
      (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hNc := norm_pos C hC
  have hNd := norm_pos D hD
  have hNe := norm_pos E hE
  have hNr := active_norm_pos C D
  have hn : nominalLog C D E (Z^M) V Z=
      Real.logb Z (E.absNorm:ℝ)+Real.logb Z (Ideal.span {activeConductor C D}).absNorm+
      2*Real.logb Z V-M-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ) := by
    unfold nominalLog
    rw [nominal_equal_support C D E hC hD heq]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    ring
  have hq0 : 0≤Real.logb Z (normValue q) := by
    apply Real.logb_nonneg hZ
    exact norm_ge_one (Ideal.span {q}) (Ideal.span_singleton_eq_bot.not.mpr hq)
  have hmove : errorMoving q Z k≤2*errorRemoval q Z k := by
    have hkR : (1:ℝ)≤k := by exact_mod_cast hk
    unfold errorMoving errorRemoval
    split_ifs <;> nlinarith
  have hnomlo : -5*B≤nominalLog C D E (Z^M) V Z := by rw [hn];linarith [(abs_le.mp hA).1]
  have hnomhi : nominalLog C D E (Z^M) V Z≤4*B := by rw [hn];linarith [(abs_le.mp hA).2]
  unfold errorCommonRadius
  constructor <;> apply Real.rpow_le_rpow_of_exponent_le hZ.le
  · linarith [le_max_right
      (Real.logb Z ((if reflected then C else D).absNorm:ℝ)-
        Real.logb Z ((if reflected then D else C).absNorm:ℝ)-2*errorRemoval q Z k+errorMoving q Z k) 0]
  · have hmax : max (Real.logb Z ((if reflected then C else D).absNorm:ℝ)-
        Real.logb Z ((if reflected then D else C).absNorm:ℝ)-2*errorRemoval q Z k+errorMoving q Z k) 0≤B := by
      apply max_le _ hB
      cases reflected <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> linarith
    linarith

/-- The literal twice-child Fourier scale, including the actual extracted
prime power. This scale admits the true source without an energy premise. -/
def firstErrorTailFourier (N : ℕ)(b V : ℝ)(C : Ideal O)(q : O)(k : ℕ)(radius : ℝ) : ℝ :=
  (b^N*V/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k)^2/radius

/-- True twice-child volume and admissibility, using the retained first
coefficient and coprimality of the extracted prime with the surviving slots. -/
theorem actual_error_tail_scale_caps {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(b Z B rad : ℝ)(hb : 1≤b)(hZ : 1<Z)(hB : 0≤B)
    (hbZ : b^N≤Z)(hr : Z^(-5*B)≤ rad)
    (s : Input α)(hn : Fintype.card α≤N)(hs : s.upper≤b)(hV : volume s≤Z^B)
    (C R : Ideal O)(B₁ : actualAllocations s.pools C)(χ : Character)(t : ℝ)
    (hne : frozenCoefficient B₁.val C R s.ν s.W s.P≠0)
    (q : O)(hq : q≠0)(k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B₁ χ t).slots i,IsCoprime (Ideal.span {q}) I)
    (Bp : actualAllocations (child s C R B₁ χ t).pools ((Ideal.span {q})^k))
    (υ : Character)(v : ℝ) :
    let u := twiceChild s C R B₁ χ t (Ideal.span {q}) k Bp υ v
    volume u≤Z^(7*B+2) ∧
      firstErrorTailFourier N b (volume s) C q k rad≤Z^(7*B+2) ∧
      (volume u)^2/rad≤firstErrorTailFourier N b (volume s) C q k rad := by
  intro u
  have hz : 0<Z := zero_lt_one.trans hZ
  have hqN : (1:ℝ)≤(Ideal.span {q}).absNorm :=
    norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hq)
  have hqpow := one_le_pow₀ (n:=k) hqN
  have hC := norm_ge_one C (allocation_ne s C B₁)
  have hh := common_volume_le N b hb s hn hs C R B₁ χ t hne
  have hv : volume u≤b^N*volume s/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k := by
    change volume (child (child s C R B₁ χ t) ((Ideal.span {q})^k) (R*C) Bp υ v)≤_
    rw [child_volume _ _ (Ideal.span_singleton_eq_bot.not.mpr hq) k hslot]
    exact div_le_div_of_nonneg_right hh (by positivity)
  have hnum : 0≤b^N*volume s/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k :=
    div_nonneg (div_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le)
      (zero_le_one.trans hC)) (by positivity)
  have hnum₁ : 0≤b^N*volume s/(C.absNorm:ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le) (zero_le_one.trans hC)
  have hfactor : b^N*volume s/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k≤Z^(B+1) := by
    calc
      _≤b^N*volume s/(C.absNorm:ℝ) := div_le_self hnum₁ hqpow
      _≤b^N*volume s := div_le_self (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le) hC
      _≤Z*Z^B := mul_le_mul hbZ hV (volume_pos s).le hz.le
      _=Z^(B+1) := by rw [Real.rpow_add hz,Real.rpow_one];ring
  have hrad : 0< rad := (Real.rpow_pos_of_pos hz _).trans_le hr
  refine ⟨(hv.trans hfactor).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)),?_,?_⟩
  · unfold firstErrorTailFourier
    calc
      _≤(Z^(B+1))^2/Z^(-5*B) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hnum hfactor 2)
          (Real.rpow_pos_of_pos hz _) hr
      _=Z^(7*B+2) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1;ring
  · unfold firstErrorTailFourier
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (volume_pos u).le hv 2) hrad.le

/-- Literal extracted-prime discarded source with arbitrary saving.
The input is an actual first label with its genuine geometric norm caps;
there is no tail, source-energy, or Fourier-admissibility premise. -/
theorem eventual_actual_first_label_error_tail {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B ξ saving : ℝ)(hCs : 1≤Cs)(hb : 1≤b)
    (hlo : 0<lo)(hhi : 0≤hi)(hB : 0≤B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input α)(R seed : Ideal O),Fintype.card α≤N → (∀i,s.M i≤Cs) → s.upper≤b →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a δ reserve t : ℝ)(_hZ : 1<Z),0≤M → M≤B → 0≤a → a≤B → 0≤δ → 0≤ reserve →
      δ+reserve≤B → |Real.logb Z (volume s)|≤B →
    ∀(reflected : Bool)(l : FirstSourceLabel),Supported l.1.1 → Supported l.1.2 →
      CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 →
      Real.logb Z (l.1.1.absNorm:ℝ)≤B → Real.logb Z (l.1.2.absNorm:ℝ)≤B →
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm≤B →
      Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm≤B →
    let C := if reflected then l.1.2 else l.1.1
    ∀(B₁ : actualAllocations s.pools C)(χ : Character),
      frozenCoefficient B₁.val C R s.ν s.W s.P≠0 →
    ∀(q : O),q≠0 → ∀k : ℕ,1≤k →
      (∀i,∀I∈(child s C R B₁ χ t).slots i,IsCoprime (Ideal.span {q}) I) →
    ∀(Bp : actualAllocations (child s C R B₁ χ t).pools ((Ideal.span {q})^k))
      (υ : Character)(v : ℝ)(Φ : 𝓢(ℝ,ℂ)),
    let u := twiceChild s C R B₁ χ t (Ideal.span {q}) k Bp υ v
    let rad := errorCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
      (nominalLog l.1.1 l.1.2 (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}) (Z^M) (volume s) Z)
      (Real.logb Z (C.absNorm:ℝ)) (3*a) δ reserve q k
    let Tsec := firstErrorTailFourier N b (volume s) C q k rad
    ‖secondDiscardedEnergy u.η u.t (original u ((R*C)*(Ideal.span {q})^k) seed).columns
      (original u ((R*C)*(Ideal.span {q})^k) seed).beta Φ rad Tsec Z ξ‖/volume u≤
      Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  have hbound := actual_twice_child_second_tail (α:=α) N Cs b lo hi (7*B+2) ξ
    (saving+12*B) hCs (zero_le_one.trans hb) hlo hhi (by positivity) hξ
  obtain ⟨F,Ct,hCt,hbound⟩ := hbound
  refine ⟨F,Ct,hCt,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (b^N)] with Z hz hbZ
  refine ⟨hz.1,?_⟩
  intro s R seed hn hm hs p hp₁ hp₂ M a δ reserve t hZ hM hMB ha haB hδ hreserve hω hA
    reflected l hC hD heq hc hd he hactive C B₁ χ hne q hq k hk hslot Bp υ v Φ u rad Tsec
  have hbox := actual_error_radius_box reflected l.1.1 l.1.2
    (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val})
    hC.1 hD.1 (subsetGenerator_supported l.1.1 l.1.2 hC l.2.val).1 heq
    Z M (volume s) a δ reserve B hZ (volume_pos s) hB hM hMB ha haB hδ hreserve hω hA
    hc hd he hactive q hq k hk
  change Z^(-5*B)≤ rad ∧ rad≤Z^(12*B) at hbox
  have hrhi := hbox.2
  have hvol : volume s≤Z^B := (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hcaps := actual_error_tail_scale_caps N b Z B rad hb hZ hB hbZ hbox.1 s hn hs hvol C R B₁ χ t hne
    q hq k hslot Bp υ v
  have hrad : 0< rad := (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le hbox.1
  have hh := hz.2 s hn hm (fun i=>(s.upper_ge i).trans hs) p hp₁ hp₂ C R seed B₁ χ t
    (Ideal.span {q}) k Bp υ v Φ rad Tsec hrad hcaps.1 hcaps.2.1 hcaps.2.2
  apply hh.trans
  calc
    _≤Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(12*B)*Z^(-(saving+12*B)) := by gcongr
    _=_ := by rw [mul_assoc,←Real.rpow_add (zero_lt_one.trans hZ),show 12*B+(-(saving+12*B))=-saving by ring]

/-- Source support alone supplies all four actual first-label norm gates.
These are uniform in the selected column and orientation. -/
theorem actual_geometry_error_tail_label_caps {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(R seed : Ideal O)(M Z ξ B : ℝ)(hZ : 1<Z)(hK : 0<Z^M)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
    Real.logb Z (l.1.1.absNorm:ℝ)≤B ∧ Real.logb Z (l.1.2.absNorm:ℝ)≤B ∧
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm≤B ∧
      Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm≤B := by
  intro l
  have hlog (i : Fin 5) : geometryExponents s R seed (Z^M) Z ξ j.1.val i≤B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2
  exact ⟨hlog 0,hlog 1,hlog 4,hlog 3⟩

def firstErrorTailRadius (reflected : Bool)(l : FirstSourceLabel)
    (Z M V a δ reserve : ℝ)(q : O)(k : ℕ) : ℝ :=
  errorCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
    (nominalLog l.1.1 l.1.2 (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
      (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}) (Z^M) V Z)
    (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) (3*a) δ reserve q k

/-- The radius used by the literal error split is exactly the physical
first-label radius used by the twice-child tail theorem. -/
theorem actual_geometry_error_tail_radius {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(R seed : Ideal O)(Z M ξ a δ reserve : ℝ)(hK : 0<Z^M)
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key))(q : O)(k : ℕ) :
    let g := geometryBranch reflected s R seed (Z^M) Z ξ hK key j
    errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog (3*a) δ reserve q k=
      firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
        Z M (volume s) a δ reserve q k := by
  rfl

lemma actual_local_error_cost_le_one (q : O)(hq : q≠0)(n : ℕ) : localErrorCost q n≤1 := by
  have hN : (1:ℝ)≤(Ideal.span {q}).absNorm := norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hq)
  have hi : ((Ideal.span {q}).absNorm:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hN
  have hi0 : 0≤((Ideal.span {q}).absNorm:ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hN)
  unfold localErrorCost
  split_ifs <;> nlinarith

/-- Genuine active extracted-allocation counting, with the literal slots
and the three actual extraction indices. -/
theorem actual_error_tail_active_card {α : Type*}[Fintype α]
    (u : Input α)(q : O)(hq : Prime (Ideal.span {q}))
    (hslot : ∀i,∀I∈u.slots i,IsCoprime (Ideal.span {q}) I)(i : Fin 3) :
    (Fintype.card (actualAllocations (activeInput u).pools ((Ideal.span {q})^(errorIndex i+1))):ℝ)≤8 := by
  have hh := actual_error_allocations_card (activeInput u).pools (Ideal.span {q}) hq
    (errorIndex i+1) (error_extracted_index_cases i) (by
      intro j I hI
      have hI' := error_active_pools_subset u (Sum.inl j) hI
      exact ⟨u.pools_ne (Sum.inl j) I hI',hslot j I hI'⟩)
  simp only [Fintype.card_coe]
  exact_mod_cast hh

/-- Genuine prime-ideal counting supplies the coarse polynomial cutoff
needed to absorb the full extracted-prime multiplicity by arbitrary saving. -/
theorem actual_error_tail_prime_card (P : Finset (Ideal O))(Z U : ℝ)(hZ : 1≤Z)(hU : 0≤U)
    (hp : ∀Q∈P,Prime Q)(hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hcap : ∀Q∈P,(Q.absNorm:ℝ)≤Z^U) :
    (Fintype.card (elementPool P):ℝ)≤128*Z^U := by
  rw [Fintype.card_coe,elementPool_card P hp hbad]
  exact DescentFiberCost.finite_ideal_count_real P (Z^U) (Real.one_le_rpow hZ hU)
    (fun Q hQ=>(hp Q hQ).ne_zero) hcap

def extractedTailSum {α : Type*}[Fintype α]
    (u : Input α)(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(Z ξ : ℝ)(P : Finset (Ideal O))
    (radius Fourier : elementPool P→Fin 3→ℝ)
    (υ : elementPool P→Fin 3→RayCharacter→ Character) : ℝ :=
  let Label := (q : elementPool P) × (i : Fin 3) × (_ψ : RayCharacter) ×
    actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1))
  let E := fun l : Label=>(Ideal.span {l.1.val})^(errorIndex l.2.1+1)
  let source := fun l : Label=>child u (E l) R
    (errorActiveAllocation u (E l) l.2.2.2) (υ l.1 l.2.1 l.2.2.1) u.t
  ∑l : Label,(16*(errorIndex l.2.1+2:ℝ)*localErrorCost l.1.val (errorIndex l.2.1)/volume (source l))*
    ‖secondDiscardedEnergy (source l).η (source l).t
      (original (source l) (R*E l) seed).columns (original (source l) (R*E l) seed).beta
      Φ (radius l.1 l.2.1) (Fourier l.1 l.2.1) Z ξ‖

lemma extracted_tail_sum_eq {α : Type*}[Fintype α]
    (u : Input α)(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(Z ξ : ℝ)(P : Finset (Ideal O))
    (radius Fourier : elementPool P→Fin 3→ℝ)
    (υ : elementPool P→Fin 3→RayCharacter→ Character) :
    extractedTailSum u R seed Φ Z ξ P radius Fourier υ=
      ∑q : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1)),
          let v := child u ((Ideal.span {q.val})^(errorIndex i+1)) R
            (errorActiveAllocation u ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) u.t
          16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
            (‖secondDiscardedEnergy v.η v.t (original v (R*(Ideal.span {q.val})^(errorIndex i+1)) seed).columns
              (original v (R*(Ideal.span {q.val})^(errorIndex i+1)) seed).beta
              Φ (radius q i) (Fourier q i) Z ξ‖/volume v) := by
  unfold extractedTailSum
  simp only [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun Bp _ => ?_
  ring

def firstExtractedTailSum {α : Type*}[Fintype α]
    (N : ℕ)(b : ℝ)(s : Input α)(reflected : Bool)(l : FirstSourceLabel)(R seed : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(Φ : 𝓢(ℝ,ℂ))(Z M a δ reserve ξ : ℝ)
    (P : Finset (Ideal O))(υ : elementPool P→Fin 3→RayCharacter→ Character) : ℝ :=
  let C := if reflected then l.1.2 else l.1.1
  let radius := fun (q : elementPool P)(i : Fin 3)=>
    firstErrorTailRadius reflected l Z M (volume s) a δ reserve q.val (errorIndex i+1)
  let Fourier := fun (q : elementPool P)(i : Fin 3)=>
    firstErrorTailFourier N b (volume s) C q.val (errorIndex i+1) (radius q i)
  extractedTailSum (child s C R B₁ χ t) (R*C) seed Φ Z ξ P radius Fourier υ

/-- All literal extracted-prime labels are counted; constants precede
both allocations, source profiles, primes, rays and independent heights. -/
theorem eventual_actual_first_label_error_tail_sum {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B U ξ saving : ℝ)(hCs : 1≤Cs)(hb : 1≤b)
    (hlo : 0<lo)(hhi : 0≤hi)(hB : 0≤B)(hU : 0≤U)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input α)(R seed : Ideal O),Fintype.card α≤N → (∀i,s.M i≤Cs) → s.upper≤b →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a δ reserve t : ℝ)(_hZ : 1<Z),0≤M → M≤B → 0≤a → a≤B → 0≤δ → 0≤ reserve →
      δ+reserve≤B → |Real.logb Z (volume s)|≤B →
    ∀(reflected : Bool)(l : FirstSourceLabel),Supported l.1.1 → Supported l.1.2 →
      CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 →
      Real.logb Z (l.1.1.absNorm:ℝ)≤B → Real.logb Z (l.1.2.absNorm:ℝ)≤B →
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun Q:CommonIndex l.1.1 l.1.2=>Q.val) l.2.val}).absNorm≤B →
      Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm≤B →
    ∀(B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))(χ : Character),
      frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0 →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤Z^U) →
      (∀q : elementPool P,∀i,∀I∈(child s (if reflected then l.1.2 else l.1.1) R B₁ χ t).slots i,
        IsCoprime (Ideal.span {q.val}) I) →
    ∀υ : elementPool P→Fin 3→RayCharacter→ Character,∀Φ : 𝓢(ℝ,ℂ),
      firstExtractedTailSum N b s reflected l R seed B₁ χ t Φ Z M a δ reserve ξ P υ≤
        Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(U-saving) := by
  have hbound := eventual_actual_first_label_error_tail (α:=α)
    N Cs b lo hi B ξ saving hCs hb hlo hhi hB hξ
  obtain ⟨F,Ct,hCt,hbound⟩ := hbound
  have hRay : 0<(Fintype.card RayCharacter:ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨F,393216*(Fintype.card RayCharacter:ℝ)*Ct,by positivity,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed hn hm hs p hp₁ hp₂ M a δ reserve t hZ hM hMB ha haB hδ hr hω hA
    reflected l hC hD heq hc hd he hactive B₁ χ hne P hp hbad hpool hslot υ Φ
  let C := if reflected then l.1.2 else l.1.1
  let first := child s C R B₁ χ t
  let Fval : ℝ := Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)
  have hFval : 0≤Fval := by dsimp only [Fval];positivity
  have hcountP := actual_error_tail_prime_card P Z U hZ.le hU hp hbad hpool
  have hpoint (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)
      (Bp : actualAllocations (activeInput first).pools ((Ideal.span {q.val})^(errorIndex i+1))) :
      let u := child first ((Ideal.span {q.val})^(errorIndex i+1)) (R*C)
        (errorActiveAllocation first ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) first.t
      let rad := firstErrorTailRadius reflected l Z M (volume s) a δ reserve q.val (errorIndex i+1)
      16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
        (‖secondDiscardedEnergy u.η u.t (original u ((R*C)*(Ideal.span {q.val})^(errorIndex i+1)) seed).columns
          (original u ((R*C)*(Ideal.span {q.val})^(errorIndex i+1)) seed).beta Φ rad
          (firstErrorTailFourier N b (volume s) C q.val (errorIndex i+1) rad) Z ξ‖/volume u)≤128*Fval := by
    have hdq := elementPool_data P hp hbad q.val q.property
    have hq : q.val≠0 := hdq.1.ne_zero
    have hh := hz.2 s R seed hn hm hs p hp₁ hp₂ M a δ reserve t hZ hM hMB ha haB hδ hr hω hA
      reflected l hC hD heq hc hd he hactive B₁ χ hne q.val hq (errorIndex i+1) (by omega)
      (hslot q) (errorActiveAllocation first ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) t Φ
    have hcoeff : 0≤16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i) ∧
        16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)≤128 := by
      have hcost := actual_local_error_cost_le_one q.val hq (errorIndex i)
      have hcost0 := localErrorCost_nonneg q.val (errorIndex i)
      rcases errorIndex_cases i with hi|hi|hi <;> rw [hi] at hcost hcost0 ⊢ <;>
        norm_num only [Nat.cast_ofNat] <;> constructor <;> nlinarith only [hcost,hcost0]
    exact (mul_le_mul_of_nonneg_left hh hcoeff.1).trans
      (mul_le_mul_of_nonneg_right hcoeff.2 hFval)
  have hcountB (q : elementPool P)(i : Fin 3) := actual_error_tail_active_card first q.val
    (hp _ (elementPool_data P hp hbad q.val q.property).2.1) (hslot q) i
  unfold firstExtractedTailSum
  rw [extracted_tail_sum_eq]
  calc
    _≤∑q : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑_Bp : actualAllocations (activeInput first).pools ((Ideal.span {q.val})^(errorIndex i+1)),128*Fval :=
      Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun i _=>Finset.sum_le_sum
        (fun ψ _=>Finset.sum_le_sum (fun Bp _=>hpoint q i ψ Bp))))
    _≤∑q : elementPool P,∑i : Fin 3,(Fintype.card RayCharacter:ℝ)*8*(128*Fval) := by
      refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun i _ => ?_
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hcountB q i) (by positivity : 0≤128*Fval))
        (show 0≤(Fintype.card RayCharacter:ℝ) from Nat.cast_nonneg _)
    _=(Fintype.card (elementPool P):ℝ)*(3*((Fintype.card RayCharacter:ℝ)*8*(128*Fval))) := by simp
    _≤(128*Z^U)*(3*((Fintype.card RayCharacter:ℝ)*8*(128*Fval))) :=
      mul_le_mul_of_nonneg_right hcountP (by positivity)
    _=_ := by
      dsimp only [Fval]
      rw [Real.rpow_sub (zero_lt_one.trans hZ),Real.rpow_neg (zero_lt_one.trans hZ).le]
      ring

/-- Complete literal extracted-prime discarded-source payment. The genuine
prime and allocation multiplicities are paid by arbitrarily strong tail
saving; the physical-D factor and original seed remain visible. -/
theorem eventual_actual_geometry_error_tail {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi slotlo B Uslot Uprime ξ εmass εcount saving : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hlo : 0<lo)(hhi : 0≤hi)(hslotlo : 0<slotlo)
    (hB : 0≤B)(hUs : 0≤Uslot)(hUp : 0≤Uprime)(hξ : 0<ξ)
    (hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Ctail : ℝ,0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input α)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card α≤N → (∀i,s.M i≤Cs) → s.upper≤b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a reserve t : ℝ)(hZ : 1<Z),0≤M → M≤B → 0≤a → a≤B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤B → Squarefree seed → seed≠0 →
      0<sourceRadius s → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^Uslot) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤Z^Uprime) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    ∀υ : (j : rows)→actualAllocations s.pools (C j)→elementPool P→Fin 3→RayCharacter→ Character,
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*
        firstExtractedTailSum N b s reflected
          (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ
          Z M a (frequencyLoss Z 32 ξ) reserve ξ P (υ j alloc))≤
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
          Z^(-saving)/(seed.absNorm:ℝ) := by
  let L : ℝ := ((N:ℝ)+2)*Uslot
  let requested : ℝ := saving+B*εmass+6*B+L+3*εcount+Uprime
  obtain ⟨F,Ct,hCt,htail⟩ := eventual_actual_first_label_error_tail_sum (α:=α)
    N Cs b lo hi B Uprime ξ requested hCs hb hlo hhi hB hUp hξ
  obtain ⟨Cw,hCw,hpayment⟩ := eventual_actual_geometry_tail_allocation_payment (ι:=α)
    N Cs b slotlo lo B Uslot ξ εmass εcount hCs hslotlo hlo hB hUs hξ.le hem hec
  refine ⟨F,Ct*Cw,mul_pos hCt hCw,?_⟩
  filter_upwards [htail,hpayment] with Z ht hw
  refine ⟨ht.1,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ M a reserve t hZ hM hMB ha haB hr hω
    hseed hseed0 hsource hcap hA hpool P hp hbad hpcap hslot reflected key hK A rows C weight υ
  have hs₁ : ∀x,s.W₁ x≠0→lo≤x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→lo≤x := by
    intro x hx;rw [hp₂] at hx;exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  let T : ℝ := Uprime-requested
  let factor : ℝ := Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hterm (j : rows)(alloc : actualAllocations s.pools (C j)) :
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*
        firstExtractedTailSum N b s reflected
          (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ
          Z M a (frequencyLoss Z 32 ξ) reserve ξ P (υ j alloc)≤
        factor*(geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) := by
    by_cases hne : frozenCoefficient alloc.val (C j) R s.ν s.W s.P≠0
    · let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1
      have hc := actual_geometry_error_tail_label_caps s R seed M Z ξ B hZ hK
        hseed hz₁ hz₂ hcap key j.val
      have hh := ht.2 s R j.val.2.1.val hn hm hs p hp₁ hp₂ M a (frequencyLoss Z 32 ξ)
        reserve t hZ hM hMB ha haB
        (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le) hr hω hA
        reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
        src.hC src.hD src.sameSupport hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) hne P hp hbad hpcap
        (fun q i I hI=>hslot q i.val I hI) (υ j alloc) Φ
      apply (mul_le_mul_of_nonneg_left hh
        (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc)).trans_eq
      dsimp only [factor,T]
      ring
    · have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc=0 := by
        simp only [geometryAllocationWeight,C,hne,ite_false]
      rw [hw0,zero_mul,zero_mul,mul_zero]
  have hpaid := hw.2 s R seed W M T hZ hn hm hl hseed hseed0 hz₁ hz₂ hsource hcap hA hM
    hs₁ hs₂ hpool reflected key
  have he : B*εmass+T+6*B+((N:ℝ)+2)*Uslot+3*εcount=-saving := by
    dsimp only [T,requested,L];ring
  rw [he] at hpaid
  calc
    _≤∑j : rows,∑alloc : actualAllocations s.pools (C j),
      factor*(geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) :=
      Finset.sum_le_sum (fun j _=>Finset.sum_le_sum (fun alloc _=>hterm j alloc))
    _=factor*(∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) := by
      simp only [Finset.mul_sum]
    _≤factor*_ := mul_le_mul_of_nonneg_left hpaid (by dsimp only [factor];positivity)
    _=_ := by dsimp only [factor];ring

end
end OAI.SevenEighths.Cycle63InitialMass
