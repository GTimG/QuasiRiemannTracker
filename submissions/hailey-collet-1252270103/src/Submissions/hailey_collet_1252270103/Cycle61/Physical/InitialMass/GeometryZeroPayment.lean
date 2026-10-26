/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryZeroFamily
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryUniformScalar
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryColumnFibres
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.FirstLowLabelCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalSource CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentWholeDivisorShell CenteredMomentDivisorBoundary CenteredMomentLogDyadic
open UniqueFactorizationMonoid CompletedGauss CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
local instance zeroPaymentDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma squarefree_moebius_norm (D : Ideal O) (hD : Squarefree D) :
    ‖(moebius D:ℂ)‖=1 := by
  simp only [hD.moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,
    norm_pow,norm_neg,norm_one,one_pow]

/-- All projectors in a dyad are counted, including projectors which never
occur in a particular source. The reciprocal norm pays this actual count. -/
lemma projector_shell_reciprocal (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1≤T)
    (hD : ∀D∈Ds,D≠0)
    (hlo : ∀D∈Ds,T≤(D.absNorm:ℝ))
    (hhi : ∀D∈Ds,(D.absNorm:ℝ)<2*T) :
    (∑D∈Ds,1/(D.absNorm:ℝ))≤256 := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hh := divisor_dyad_card Ds T hT hD hhi
  calc
    _≤∑D∈Ds,1/T := Finset.sum_le_sum (fun D hd=>
      div_le_div_of_nonneg_left zero_le_one hTp (hlo D hd))
    _=(Ds.card:ℝ)/T := by simp [div_eq_mul_inv]
    _≤256 := (div_le_iff₀ hTp).mpr (by simpa using hh)

theorem eventual_projector_reciprocal (B ε : ℝ)(hB : 0≤B)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,(D.absNorm:ℝ)≤Z^B) →
      (∑D∈Ds,1/(D.absNorm:ℝ))≤C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := selected_card_subpower B ε hB hε
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds hs hn
  have hweighted : (∑D∈Ds,1/(D.absNorm:ℝ))=
      ∑D∈Ds,‖(moebius D:ℂ)‖*(1/(D.absNorm:ℝ)) := by
    apply Finset.sum_congr rfl
    intro D hd
    rw [squarefree_moebius_norm D (hs D hd),one_mul]
  rw [hweighted,sum_norm_moebius_shells]
  calc
    _≤∑n∈selectedShells Ds,(256:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn'
      have hT := (selected_scale_bounds Ds (Z^B) (fun D hd _=>hn D hd) n hn').1
      have hnorm : (∑D∈shell Ds n,‖(moebius D:ℂ)‖*
          (1/(D.absNorm:ℝ)))=∑D∈shell Ds n,1/(D.absNorm:ℝ) := by
        apply Finset.sum_congr rfl
        intro D hd
        rw [squarefree_moebius_norm D (shell_member_data Ds n D hd).2.2.1,one_mul]
      rw [hnorm]
      exact projector_shell_reciprocal _ _ hT
        (fun D hd=>(shell_member_data Ds n D hd).2.2.2.1)
        (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.1)
        (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.2)
    _=((selectedShells Ds).card:ℝ)*256 := by simp
    _≤(C*Z^ε)*256 := mul_le_mul_of_nonneg_right
      (hz.2 Ds (fun D hd _=>hn D hd)) (by norm_num)
    _=(256*C)*Z^ε := by ring

/-- The full first-label family is counted with its original seed. The
residual projectors are independent of those labels and retain their norm. -/
theorem eventual_first_zero_label_projector_payment (B L ε : ℝ)
    (hB : 0≤B)(hL : 0≤L)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(p E factor : ℝ),p≤B → 0≤factor →
      ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,(D.absNorm:ℝ)≤Z^L) →
      (∑_l∈labels,∑D∈Ds,factor*Z^(E-p)/(D.absNorm:ℝ))≤
        C*factor*Z^(E+2*ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := actual_first_low_label_count B ε hB hε
  obtain ⟨D,hD,hprojector⟩ := eventual_projector_reciprocal L ε hL hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  filter_upwards [hprojector] with Z hz
  refine ⟨hz.1,?_⟩
  intro p E factor hp hf seed hs hs0 labels hsup heq hseed hnorm hrad Ds hDs hcap
  have hc := hcount Z hz.1.le p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hd := hz.2 Ds hDs hcap
  have hZp : 0<Z := zero_lt_one.trans hz.1
  calc
    _=(labels.card:ℝ)*(factor*Z^(E-p))*(∑D∈Ds,1/(D.absNorm:ℝ)) := by
      simp only [div_eq_mul_inv,←Finset.mul_sum,Finset.sum_const,
        nsmul_eq_mul,one_mul]; ring
    _≤(C*Z^(p+ε)/(seed.absNorm:ℝ))*(factor*Z^(E-p))*(D*Z^ε) := by
      gcongr
    _=(C*D)*factor*(Z^(p+ε)*Z^(E-p)*Z^ε)/(seed.absNorm:ℝ) := by ring
    _=(C*D)*factor*Z^(E+2*ε)/(seed.absNorm:ℝ) := by
      have he : Z^(p+ε)*Z^(E-p)*Z^ε=Z^(E+2*ε) := by
        rw [←Real.rpow_add hZp,←Real.rpow_add hZp]
        congr 1; ring
      rw [he]


def zeroPaymentExponent (Z M A a ξ reserve padding ε εmass B : ℝ) : ℝ :=
  a-M*(8754683599/120632400000)+frequencyLoss Z 32 ξ+reserve+
    ε*(A+padding)+B*εmass

lemma actual_zero_exponent_payment {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(R seed : Ideal O)(K Z ξ A M a reserve padding ε εmass B : ℝ)
    (hK : 0<K)(hZ : 1<Z)(hε : 0≤ε)(hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(hsource : sourceRadius s≤Z^B)
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    let v := geometryExponents s R seed K Z ξ j.1.val
    let l := geometryFirstLabel s R seed K Z ξ hK key j
    firstZeroReference reflected Z A a l+
      firstZeroSaving reflected Z M A ξ reserve padding ε
        (Real.logb Z (j.2.1.val.absNorm:ℝ)) l+B*εmass-
      (if reflected then rightExponent A v else leftExponent A v)≤
      zeroPaymentExponent Z M A a ξ reserve padding ε εmass B-v 2-
        Real.logb Z (j.2.1.val.absNorm:ℝ) := by
  intro v l
  have hc (i : Fin 5) : 0≤v i := Real.logb_nonneg hZ
    (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val i).1
  have he : Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=v 4 := by
    change Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm
    rw [first_projector_span]
  have hR : Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm=v 3 := by rfl
  have hC : Real.logb Z (l.1.1.absNorm:ℝ)=v 0 := by rfl
  have hD : Real.logb Z (l.1.2.absNorm:ℝ)=v 1 := by rfl
  cases reflected <;>
    simp only [firstZeroReference,firstZeroSaving,Bool.false_eq_true,ite_false,ite_true,
      hR,he,hC,hD,leftExponent,rightExponent,zeroPaymentExponent] <;>
    nlinarith [mul_nonneg hε (hc 0),mul_nonneg hε (hc 1),
      le_max_left (3*v 0-5*v 1-v 3) 0,le_max_right (3*v 0-5*v 1-v 3) 0,
      le_max_left (3*v 1-5*v 0-v 3) 0,le_max_right (3*v 1-5*v 0-v 3) 0]

lemma zero_cost_power_payment (Z mass factor power S gain E p L : ℝ)
    (hZ : 1<Z)(hL : 0<L)(hfactor : 0≤factor)
    (hmass : mass≤factor*Z^gain/Z^S)
    (hexp : power+gain-S≤E-p-Real.logb Z L) :
    mass*Z^power≤factor*Z^(E-p)/L := by
  have hz := zero_lt_one.trans hZ
  calc
    _≤(factor*Z^gain/Z^S)*Z^power :=
      mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hz.le _)
    _=factor*Z^(power+gain-S) := by
      rw [Real.rpow_sub hz,Real.rpow_add hz];ring
    _≤factor*Z^(E-p-Real.logb Z L) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) hfactor
    _=factor*Z^(E-p)/L := by
      rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hL];ring

/-- The literal mass in the zero-family sum has the two complementary
physical-D factors. The fixed support constant precedes the moving source. -/
theorem actual_geometry_zero_cost_payment {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(lo a₁ a₂ : ℝ)(hlo : 0<lo)(ha₁ : 0<a₁)(ha₂ : 0<a₂)
    (s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))
    (M Z ξ a reserve padding ε εmass B : ℝ)(hZ : 1<Z)
    (hn : Fintype.card ι≤N)(hl : lo≤s.lower)(hε : 0≤ε)(hem : 0≤εmass)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x)(hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
    let factor := if reflected then 1/geometryDCompensator key else
      2*(geometrySupportConstant N lo a₁ a₂)^2*geometryDCompensator key
    ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hK key
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2*
      ((geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j).absNorm:ℝ)^(εmass-1)*
      Z^(firstZeroReference reflected Z A a l+firstZeroSaving reflected Z M A ξ reserve
        padding ε (Real.logb Z (j.2.1.val.absNorm:ℝ)) l)≤
      factor*Z^(zeroPaymentExponent Z M A a ξ reserve padding ε εmass B-v 2)/
        (j.2.1.val.absNorm:ℝ) := by
  intro hK A v l factor
  have hH := (geometryDCompensator_pos key).le
  have hZle := hZ.le
  have hL : 0<(j.2.1.val.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (actual_first_divisor_ne_zero (geometryFirstSource s R seed (Z^M) Z ξ hK key j.1) j.2.1))
  have hpow := actual_zero_exponent_payment s R seed (Z^M) Z ξ A M a reserve padding
    ε εmass B hK hZ hε hs hz₁ hz₂ hsource reflected key j
  apply zero_cost_power_payment Z _ factor _
    (if reflected then rightExponent A v else leftExponent A v) (B*εmass)
    (zeroPaymentExponent Z M A a ξ reserve padding ε εmass B) (v 2) _ hZ hL
    (by dsimp only [factor];split <;> positivity)
  · cases reflected
    · have hh := actual_geometry_left_mass_compensation s R seed W M Z ξ B εmass hZ
        hem hs hz₁ hz₂ hsource a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j
      have hc := actual_geometry_support_constant s N lo a₁ a₂ hn hlo hl ha₁ ha₂
      apply hh.trans
      dsimp only [factor,A,v]
      simp only [Bool.false_eq_true,ite_false]
      have hcc0 := hc.1
      have hcc := hc.2
      gcongr; first | assumption | exact le_rfl
    · have hh := actual_geometry_right_mass_compensation s R seed (Z^M) Z ξ M A B
        εmass hK hZ hem hs hz₁ hz₂ hsource key
        (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j
      simpa only [factor,v,ite_true,one_div,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,one_mul] using hh
  · exact hpow


lemma selected_zero_pairs (pairs : Finset (FirstSourceLabel×Ideal O))
    (G : ℝ)(hG : 0≤G) :
    (∑q : pairs,G/(q.val.2.absNorm:ℝ))≤
      ∑_l∈pairs.image Prod.fst,∑D∈pairs.image Prod.snd,G/(D.absNorm:ℝ) := by
  rw [Finset.sum_coe_sort pairs (fun q=>G/(q.2.absNorm:ℝ)),
    ←Finset.sum_product (pairs.image Prod.fst) (pairs.image Prod.snd)
      (fun q : FirstSourceLabel×Ideal O=>G/(q.2.absNorm:ℝ))]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,
      Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  · intro q _ _
    exact div_nonneg hG (Nat.cast_nonneg _)

/-- Four first dyads, both rays, the complete first arithmetic labels and
all residual projector dyads are paid before any column cost is chosen. -/
theorem eventual_actual_zero_column_payment {ι : Type*}[Fintype ι][DecidableEq ι]
    (Amax Dmax B L ξ ε : ℝ)(hA : 0≤Amax)(hD : 0≤Dmax)(hB : 0≤B)
    (hL : 0≤L)(hξ : 0≤ξ)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ)(hK : 0<K)
        (key : ℤ×(Fin 5→ℤ)),Squarefree seed → seed≠0 →
      s.W₁ 0=0 → s.W₂ 0=0 → 0<sourceRadius s → sourceRadius s≤Z^B →
      volume s≤Z^Amax → K⁻¹≤Z^Dmax →
      ∀rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)),
      (∀r∈rows,Squarefree r.2.1.val) →
      (∀r∈rows,(r.2.1.val.absNorm:ℝ)≤Z^L) →
      ∀(factor E : ℝ)(cost : rows→ℝ),0≤factor → (∀r,0≤cost r) →
      (∀r,cost r≤factor*Z^(E-geometryExponents s R seed K Z ξ r.val.1.val 2)/
        (r.val.2.1.val.absNorm:ℝ)) →
      (∑r : rows,cost r)≤C*factor*Z^(E+3*ε)/(seed.absNorm:ℝ) := by
  obtain ⟨Cd,hCd,hdyad⟩ := actual_first_selected_column_budget (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  obtain ⟨Cl,hCl,hlabels⟩ := eventual_first_zero_label_projector_payment B L ε hB hL hε
  refine ⟨2*Cl*Cd,by positivity,?_⟩
  filter_upwards [hdyad,hlabels] with Z hd hl
  refine ⟨hl.1,?_⟩
  intro s R seed K hK key hs hs0 hz₁ hz₂ hsource hcap hV hKi rows hsq hpool
    factor E cost hf hc hcost
  have hZle := hl.1.le
  let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key r.val,r.val.2.1.val)
  let pairs := Finset.univ.image code
  let labels := pairs.image Prod.fst
  let Ds := pairs.image Prod.snd
  let p₀ : ℝ := (key.2 2:ℝ)*Real.logb Z 2
  let p₁ : ℝ := min B (((key.2 2:ℝ)+1)*Real.logb Z 2)
  have hwitness (q : FirstSourceLabel×Ideal O)(hq : q∈pairs) :
      ∃r : rows,code r=q := by
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hq
    exact ⟨r,hr⟩
  have hlwitness (l : FirstSourceLabel)(hl' : l∈labels) :
      ∃r : rows,geometryFirstLabel s R seed K Z ξ hK key r.val=l := by
    obtain ⟨q,hq,hq'⟩ := Finset.mem_image.mp hl'
    obtain ⟨r,hr⟩ := hwitness q hq
    exact ⟨r,(congrArg Prod.fst hr).trans hq'⟩
  have hlabel (r : rows) := CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource
      (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ r.val.1.val.1.property
  have hcommon (r : rows) := actual_common_gates s R seed hs hz₁ hz₂
    r.val.1.val.1.val.1 r.val.1.val.1.val.2 r.val.1.val.1.property
  have hrange (r : rows) := actual_geometry_fiber_range s R seed K Z ξ B
    hl.1 hs hz₁ hz₂ hcap key r.val.1 2
  have hrad (r : rows) :
      ((commonRadical (code r).1.1.1 (code r).1.1.2).absNorm:ℝ)≤Z^p₁ := by
    have hnorm := (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hcap r.val.1.val 2).2
    have hp : (geometryNorms s R seed K Z ξ r.val.1.val 2)≤
        Z^(((key.2 2:ℝ)+1)*Real.logb Z 2) := by
      have hpos := (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hcap r.val.1.val 2).1
      have hh := Real.rpow_le_rpow_of_exponent_le hl.1.le (hrange r).2.le
      rw [geometryExponents,Real.rpow_logb (zero_lt_one.trans hl.1) hl.1.ne'
        (zero_lt_one.trans_le hpos)] at hh
      exact hh
    dsimp only [p₁]
    rcases le_total B (((key.2 2:ℝ)+1)*Real.logb Z 2) with hb | hb
    · rw [min_eq_left hb];exact hnorm
    · rw [min_eq_right hb];exact hp
  have hbudget := hl.2 p₁ (E+p₁-p₀) factor (min_le_left _ _) hf seed hs hs0 labels
    (by intro l h;obtain ⟨r,rfl⟩:=hlwitness l h;exact hlabel r)
    (by intro l h;obtain ⟨r,rfl⟩:=hlwitness l h;exact (hcommon r).2.2.1)
    (by intro l h;obtain ⟨r,rfl⟩:=hlwitness l h;exact ⟨(hcommon r).2.2.2.1,(hcommon r).2.2.2.2.1⟩)
    (by intro l h;obtain ⟨r,rfl⟩:=hlwitness l h;exact
      ⟨(hcommon r).2.2.2.2.2.1.trans hcap,(hcommon r).2.2.2.2.2.2.trans hcap⟩)
    (by intro l h;obtain ⟨r,rfl⟩:=hlwitness l h;exact hrad r) Ds
    (by
      intro D h;obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨r,rfl⟩:=hwitness q hq;exact hsq r.val r.property)
    (by
      intro D h;obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨r,rfl⟩:=hwitness q hq;exact hpool r.val r.property)
  have hpower : Z^(E+p₁-p₀+2*ε)≤2*Z^(E+2*ε) := by
    have hp : p₁-p₀≤Real.logb Z 2 := by
      have hm := min_le_right B (((key.2 2:ℝ)+1)*Real.logb Z 2)
      dsimp only [p₁,p₀];linarith
    have hh := Real.rpow_le_rpow_of_exponent_le hl.1.le
      (show E+p₁-p₀+2*ε≤E+2*ε+Real.logb Z 2 by linarith)
    apply hh.trans_eq
    rw [Real.rpow_add (zero_lt_one.trans hl.1),Real.rpow_logb
      (zero_lt_one.trans hl.1) hl.1.ne' (by norm_num : (0:ℝ)<2)]
    ring
  have hjoint : ∀pick : pairs → ↥rows,(∀j,code (pick j)=j.val) →
      (∑j : pairs,cost (pick j))≤2*Cl*factor*Z^(E+2*ε)/(seed.absNorm:ℝ) := by
    intro pick hpick
    calc
      _≤∑q : pairs,factor*Z^(E-p₀)/(q.val.2.absNorm:ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        apply (hcost (pick q)).trans
        have hp := (hrange (pick q)).1
        have hnorm := congrArg Prod.snd (hpick q)
        change (pick q).val.2.1.val=q.val.2 at hnorm
        rw [hnorm]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZle (by dsimp only [p₀];linarith)) hf)
          (Nat.cast_nonneg _)
      _≤∑l∈labels,∑D∈Ds,factor*Z^(E-p₀)/(D.absNorm:ℝ) :=
        selected_zero_pairs pairs _ (mul_nonneg hf (Real.rpow_nonneg (zero_lt_one.trans hl.1).le _))
      _=∑l∈labels,∑D∈Ds,factor*Z^((E+p₁-p₀)-p₁)/(D.absNorm:ℝ) := by
        rw [show (E+p₁-p₀)-p₁=E-p₀ by ring]
      _≤Cl*factor*Z^(E+p₁-p₀+2*ε)/(seed.absNorm:ℝ) := hbudget
      _≤Cl*factor*(2*Z^(E+2*ε))/(seed.absNorm:ℝ) := by gcongr
      _=2*Cl*factor*Z^(E+2*ε)/(seed.absNorm:ℝ) := by ring
  have hh := hd.2 s R seed K hK key hs hz₁ hz₂ hsource hcap hV hKi rows cost
    (2*Cl*factor*Z^(E+2*ε)/(seed.absNorm:ℝ)) hc hjoint
  apply hh.trans_eq
  have hp : Z^ε*Z^(E+2*ε)=Z^(E+3*ε) := by
    rw [←Real.rpow_add (zero_lt_one.trans hl.1)]
    congr 1;ring
  calc
    _=(2*Cl*Cd)*factor*(Z^ε*Z^(E+2*ε))/(seed.absNorm:ℝ) := by ring
    _=_ := by rw [hp]


/-- This is the remaining literal sum in `actual_geometry_zero_family`.
No zero-energy estimate is assumed: the mass and exponent gates are proved
from the actual scalar, physical-D bin and original arithmetic labels. -/
theorem eventual_actual_geometry_zero_mass_payment {ι : Type*}[Fintype ι][DecidableEq ι]
    (Amax Dmax B L ξ εcount : ℝ)(hA : 0≤Amax)(hD : 0≤Dmax)(hB : 0≤B)
    (hL : 0≤L)(hξ : 0≤ξ)(hec : 0<εcount)
    (N : ℕ)(lo a₁ a₂ : ℝ)(hlo : 0<lo)(ha₁ : 0<a₁)(ha₂ : 0<a₂) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))
        (M a reserve padding εzero εmass : ℝ)(hZ : 1<Z),
      Fintype.card ι≤N → lo≤s.lower → 0≤εzero → 0≤εmass →
      Squarefree seed → seed≠0 → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^Amax →
      (Z^M)⁻¹≤Z^Dmax →
      (∀x,s.W₁ x≠0→a₁≤x) → (∀x,s.W₂ x≠0→a₂≤x) →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
      let A := Real.logb Z (volume s)
      let factor := if reflected then 1/geometryDCompensator key else
        2*(geometrySupportConstant N lo a₁ a₂)^2*geometryDCompensator key
      ∀rows : Finset (FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)),
      rows⊆firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus) →
      (∀r∈rows,(r.2.1.val.absNorm:ℝ)≤Z^L) →
      (∑j : rows,‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hK key
          (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j.val‖^2*
        ((geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val).absNorm:ℝ)^(εmass-1)*
        Z^(firstZeroReference reflected Z A a (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)+
          firstZeroSaving reflected Z M A ξ reserve padding εzero
            (Real.logb Z (j.val.2.1.val.absNorm:ℝ))
            (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)))≤
      C*factor*Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/
        (seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := eventual_actual_zero_column_payment (ι:=ι)
    Amax Dmax B L ξ εcount hA hD hB hL hξ hec
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W M a reserve padding εzero εmass hZ hn hl hezero hem hs hs0
    hz₁ hz₂ hsource hcap hV hKi hs₁ hs₂ reflected key hK A factor rows hlive hpool
  have hH := (geometryDCompensator_pos key).le
  apply hz.2 s R seed (Z^M) hK key hs hs0 hz₁ hz₂ hsource hcap hV hKi rows
    (fun r hr=>actual_first_live_squarefree _ _ r (hlive hr)) hpool factor
    (zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B) _
    (by dsimp only [factor];split <;> positivity)
    (by intro r;positivity)
  intro r
  exact actual_geometry_zero_cost_payment N lo a₁ a₂ hlo ha₁ ha₂ s R seed W
    M Z ξ a reserve padding εzero εmass B hZ hn hl hezero hem hs hz₁ hz₂ hcap hs₁ hs₂
    reflected key r.val


/-- Padded original pools also count: no nonzero-coefficient assertion is
used to bound the literal residual projector. -/
theorem actual_geometry_projector_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(N : ℕ)(R seed : Ideal O)(K Z ξ U : ℝ)(hK : 0<K)
    (hN : Fintype.card ι≤N)(hZ : 1≤Z)(hU : 0≤U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    (j.2.1.val.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  have hp := actual_finite_pool_cap s N Z U hN hZ hU hpool
  exact (first_divisor_norm (geometryFirstSource s R seed K Z ξ hK key j.1)
    _ hp j.2.1).2

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.projector_shell_reciprocal
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_projector_reciprocal
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_first_zero_label_projector_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_zero_exponent_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_zero_cost_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_zero_column_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_zero_mass_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_projector_cap
