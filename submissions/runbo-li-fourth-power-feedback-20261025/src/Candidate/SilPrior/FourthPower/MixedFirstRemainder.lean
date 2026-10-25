/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first-Poisson zero and discarded terms, including the selected
twist and the literal positive selected average. These are FIRST-sector
remainders, not the localized second-Poisson density. Parent checks Lean.
-/
import Candidate.SilPrior.FourthPower.MixedFirstPhysicalApplication
import Candidate.SilPrior.FourthPower.MixedFirstLiveRemainders
import Candidate.SilPrior.FourthPower.MixedSelectedVolume
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailAggregate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstRemainder
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceRow
open CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstSectorTail CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform (kernel_inverse_cap eventually_tail_threshold)
open EisensteinSchwartzPoisson QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedInnerExceptionalBlock MixedFirstLiveRemainders
open MixedFirstPhysicalApplication
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem selected_coefficient_norm (s : Source ι a b) (ha : 0<a) (seed F I : Id) :
    ‖selectedCoefficient s ha seed F I‖≤‖sourceCoefficient s ha seed I‖ := by
  rw [selectedCoefficient,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (selectedTwist_norm F I)

theorem selected_mass (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (seed F : Id) :
    (∑I∈sourceColumns s,‖selectedCoefficient s ha seed F I‖)≤massCap s :=
  (Finset.sum_le_sum (fun I _=>selected_coefficient_norm s ha seed F I)).trans
    (original_coefficient_mass s ha hb seed)

theorem selected_cap (s : Source ι a b) (ha : 0<a) (seed F I : Id)
    (hi : selectedCoefficient s ha seed F I≠0) :
    I≠0 ∧ (I.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d :=
  original_coefficient_cap s ha seed I (selected_support s ha seed F I hi)

/-- The selected multiplier can be moved onto each tuple exactly;
the original tuple restriction, puncture and seed remain untouched. -/
theorem selected_tuple_column (s : Source ι a b) (ha : 0<a) (seed F I : Id) :
    finiteColumnCoefficient (Fintype.piFinset (tuplePools s))
      (fun x=>originalTuple s ha seed x*selectedTwist F (finiteTupleProduct x)) I=
    selectedCoefficient s ha seed F I := by
  change (∑x∈(Fintype.piFinset (tuplePools s)).filter (fun x=>finiteTupleProduct x=I),
      originalTuple s ha seed x*selectedTwist F (finiteTupleProduct x))=
    (∑x∈(Fintype.piFinset (tuplePools s)).filter (fun x=>finiteTupleProduct x=I),
      originalTuple s ha seed x)*selectedTwist F I
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- One actual first zero bound, before any selected averaging.
The coefficient estimate is supplied by the original literal tuple. -/
theorem actual_first_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀(seed F : Id)(η : Character)(m A : O)
      (t K Y : ℝ)(Φ : 𝓢(ℝ,ℂ)),0≤K→1≤Y→sourceNormCap s.P b s.T s.d≤Y→
      ‖zeroEnergy η m A t (sourceColumns s) (selectedCoefficient s ha seed F) Φ K‖≤
        C*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*Y^(1+ε) := by
  obtain ⟨C,hC,hzero⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι instι a b s hcard ha seed F η m A t K Y Φ hK hY hcap
  let β := fun x=>originalTuple s ha seed x*selectedTwist F (finiteTupleProduct x)
  have he : finiteColumnCoefficient (Fintype.piFinset (tuplePools s)) β=
      selectedCoefficient s ha seed F := funext (selected_tuple_column s ha seed F)
  have hβ (x) (hx : x∈Fintype.piFinset (tuplePools s)) (hx0 : finiteTupleProduct x≠0) :
      ‖β x‖≤profileCap s := by
    rw [show β x=originalTuple s ha seed x*selectedTwist F (finiteTupleProduct x) from rfl,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (selectedTwist_norm _ _)).trans
      (original_tuple_norm s ha seed x)
  have hh := hzero hcard η m A t (Fintype.piFinset (tuplePools s)) β Φ Y K
    (profileCap s) hY hK (profileCap_nonneg s) hβ (fun I _ hi=>by
      rw [he] at hi
      exact (selected_cap s ha seed F I hi).2.trans hcap)
  simpa only [he,sourceColumns] using hh

theorem first_zero_normalization (s : Source ι a b) (hb : 0<b) (ε : ℝ) :
    (sourceNormCap s.P b s.T s.d)^(1+ε)/sourceVolume s=
      (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε := by
  have hv := sourceVolume_pos s
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have he : sourceNormCap s.P b s.T s.d=
      b^2*(2:ℝ)^Fintype.card ι*sourceVolume s/pairNorm s.d := by
    rw [source_cap_factored]
    unfold sourceVolume
    rw [←s.hpX]
    ring
  have hy : 0<sourceNormCap s.P b s.T s.d := by rw [he];positivity
  rw [Real.rpow_add hy,Real.rpow_one]
  conv_lhs => lhs;lhs;rw [he]
  field_simp [hv.ne',hp.ne']
  <;> ring

private theorem source_cap_nonneg (s : Source ι a b) :
    0≤sourceNormCap s.P b s.T s.d := by
  have he : sourceNormCap s.P b s.T s.d=
      b^2*(2:ℝ)^Fintype.card ι*sourceVolume s/pairNorm s.d := by
    rw [source_cap_factored]
    unfold sourceVolume
    rw [←s.hpX]
    ring
  rw [he]
  exact div_nonneg (mul_nonneg
    (mul_nonneg (sq_nonneg b) (pow_nonneg (by norm_num) _))
    (sourceVolume_pos s).le) (pairNorm_pos s.hd.1 s.hd.2).le

/-- The normalized first zero keeps the full original prefix saving.
Subunit source support is handled by literal vanishing, not max(1,Y). -/
theorem normalized_first_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,0<b→∀(seed F : Id)(η : Character)(m A : O)
      (t K : ℝ)(Φ : 𝓢(ℝ,ℂ)),0≤K→
      ‖zeroEnergy η m A t (sourceColumns s) (selectedCoefficient s ha seed F) Φ K‖/sourceVolume s≤
        C*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*
          (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε := by
  obtain ⟨C,hC,hzero⟩ := actual_first_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι instι a b s hcard ha hb seed F η m A t K Φ hK
  have hv := sourceVolume_pos s
  have hp := pairNorm_pos s.hd.1 s.hd.2
  by_cases hy : 1≤sourceNormCap s.P b s.T s.d
  · have hh := div_le_div_of_nonneg_right
      (hzero ι a b s hcard ha seed F η m A t K _ Φ hK hy le_rfl) hv.le
    apply hh.trans_eq
    rw [mul_div_assoc,first_zero_normalization s hb ε]
    ring
  · have hz (I : Id) : selectedCoefficient s ha seed F I=0 := by
      by_contra hi
      have hh := selected_cap s ha seed F I hi
      exact hy ((ideal_norm_one_le hh.1).trans hh.2)
    simp only [zeroEnergy,hz,zero_mul,mul_zero,Finset.sum_const_zero,norm_zero,zero_div]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (sq_nonneg _)) (norm_nonneg _))
        (div_nonneg (mul_nonneg (sq_nonneg b) (pow_nonneg (by norm_num) _)) hp.le))
      (Real.rpow_nonneg (source_cap_nonneg s) _)

/-- The finite source radius is a fixed multiple of volume, uniformly
before every profile, height, selected ideal and original prefix. -/
def supportHeight (N : ℕ) (b : ℝ) : ℝ := Real.log (max 1 (b^2*(2:ℝ)^N))

theorem source_cap_volume (s : Source ι a b) (N : ℕ) (hN : Fintype.card ι≤N) :
    sourceNormCap s.P b s.T s.d≤Real.exp (supportHeight N b)*sourceVolume s := by
  have hv := sourceVolume_pos s
  have hp1 : (1:ℝ)≤pairNorm s.d :=
    one_le_mul_of_one_le_of_one_le (ideal_norm_one_le s.hd.1) (ideal_norm_one_le s.hd.2)
  have he : Real.exp (supportHeight N b)=max 1 (b^2*(2:ℝ)^N) := by
    unfold supportHeight
    exact Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))
  rw [source_cap_factored,←s.hpX]
  change b^2*(2:ℝ)^Fintype.card ι*(sourceVolume s/pairNorm s.d)≤_
  calc
    _≤b^2*(2:ℝ)^N*sourceVolume s := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hN) (sq_nonneg b))
      (div_le_self hv.le hp1) (by positivity) (by positivity)
    _≤_ := by rw [he];exact mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le

/-- Exact first-sector tail with the actual selected coefficient.
No second-density replacement, K4 factor, or extra 1/W is introduced. -/
theorem actual_first_discarded (Adec N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,0≤b→∀(seed F : Id)(η : Character)(m A : O)
      (t K Tsec Z ξ : ℝ)(Φ : 𝓢(ℝ,ℂ)),0<K→1<Z→
      (sourceVolume s)^2/K≤Tsec→
      2*supportHeight N b/Real.log Z+Real.log (4:ℝ)/Real.log Z<ξ/4→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t
        (sourceColumns s) (selectedCoefficient s ha seed F) Φ K (sourceVolume s) Z ξ‖≤
      (massCap s)^2*(Real.exp (supportHeight N b)*sourceVolume s)^ε*K*
        (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec (supportHeight N b)))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨control,C,hC,htail⟩ := local_discarded_energy_bound Adec ε hε
  refine ⟨control,C,hC,?_⟩
  intro ι instι a b s hN ha hb seed F η m A t K Tsec Z ξ Φ hK hZ hscale hthreshold
  have ht := htail η m A t (sourceColumns s) (selectedCoefficient s ha seed F) Φ K
    (sourceVolume s) (supportHeight N b) Tsec Z 1 ξ hK (sourceVolume_pos s) hZ le_rfl
    (fun I _ hi=>(selected_cap s ha seed F I hi).2.trans (source_cap_volume s N hN)) hscale
    (by simpa only [mul_one] using hthreshold)
  let factor := (Real.exp (supportHeight N b)*sourceVolume s)^ε*K*
    (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (kernelReference Tsec (supportHeight N b)))^2*(1+Z^(ξ/4))^Adec)
  have hf : 0≤factor := by
    have := (sourceVolume_pos s).le
    have := (show 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ from apply_nonneg _ _)
    dsimp only [factor]
    positivity
  have hm := pow_le_pow_left₀
    (Finset.sum_nonneg (fun I _=>norm_nonneg (selectedCoefficient s ha seed F I)))
    (selected_mass s ha hb seed F) 2
  apply ht.trans
  calc
    _=(∑I∈sourceColumns s,‖selectedCoefficient s ha seed F I‖)^2*factor := by dsimp only [factor];ring
    _≤(massCap s)^2*factor := mul_le_mul_of_nonneg_right hm hf
    _=_ := by dsimp only [factor];ring

/-- A fixed arbitrary-saving tail order. The support factor V at
epsilon=1 cancels the one outside source normalization exactly. -/
theorem choose_first_tail_order (B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃Adec : ℕ,∀(Z H Vmass K : ℝ),1≤Z→0≤Vmass→0<K→
      Vmass≤Z^B→K≤Z^B→
      Vmass^2*K*((min 1 (kernelReference (Z^(3*B)) H))^2)⁻¹*
        ((1+Z^(ξ/4))^Adec)⁻¹≤(1+Real.exp (2*H))^2*Z^(-saving) := by
  obtain ⟨Adec,hAdec⟩ := exists_nat_ge ((9*B+saving)/(ξ/4))
  have horder : 9*B-(ξ/4)*(Adec:ℝ)≤-saving := by
    have hh := (div_le_iff₀ (by linarith : 0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro Z H Vmass K hZ hm hK hmc hKc
  have hz := zero_lt_one.trans_le hZ
  have hkernel := kernel_inverse_cap H Z (3*B) (Z^(3*B)) hZ (by positivity)
    (Real.rpow_pos_of_pos hz _) le_rfl
  have hdecay := reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^2*Z^B*((1+Real.exp (2*H))^2*(Z^(3*B))^2)*Z^(-(ξ/4)*(Adec:ℝ)) := by
      gcongr <;> first | assumption | positivity
    _=(1+Real.exp (2*H))^2*Z^(9*B-(ξ/4)*(Adec:ℝ)) := by
      rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le]
      calc
        _=(1+Real.exp (2*H))^2*
            ((Z^(B*2)*Z^B*Z^((3*B)*2))*Z^(-(ξ/4)*(Adec:ℝ))) := by norm_num only [Nat.cast_ofNat];ring
        _=_ := by
          rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
          congr 2
          ring
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

/-- Arbitrary saving for the actual first discarded term, after the
single source-volume normalization. Polynomial inputs are explicit
finite numerical quantities already supplied by MixedFirstCutoffs. -/
theorem normalized_first_tail (N : ℕ) (b B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,Fintype.card ι≤N→
      ∀ha : 0<a,0≤b→∀(seed F : Id)(η : Character)(m A : O)(t K : ℝ)(Φ : 𝓢(ℝ,ℂ)),
      0<K→poolCap s≤Z^B→sourceVolume s≤Z^B→K≤Z^B→K⁻¹≤Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t
        (sourceColumns s) (selectedCoefficient s ha seed F) Φ K (sourceVolume s) Z ξ‖/sourceVolume s≤
      C*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨Adec,horder⟩ := choose_first_tail_order B ξ saving hB hξ
  obtain ⟨control,C0,hC0,htail⟩ := actual_first_discarded Adec N 1 (by norm_num)
  let H := supportHeight N b
  refine ⟨control,C0*Real.exp H*(1+Real.exp (2*H))^2,by positivity,?_⟩
  filter_upwards [eventually_tail_threshold H ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a s hN ha hb seed F η m A t K Φ hK hpool hV hKcap hKinv
  have hz := zero_lt_one.trans hZ.1
  have hv := sourceVolume_pos s
  have hscale : (sourceVolume s)^2/K≤Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hv.le hV 2) hKinv
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have ht := htail ι a b s hN ha hb seed F η m A t K (Z^(3*B)) Z ξ Φ
    hK hZ.1 hscale hZ.2
  have hn := horder Z H (poolCap s) K hZ.1.le (poolCap_nonneg s) hK hpool hKcap
  have hc : 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply (div_le_div_of_nonneg_right ht hv.le).trans
  calc
    _=(C0*Real.exp H*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        ((poolCap s)^2*K*((min 1 (kernelReference (Z^(3*B)) H))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹) := by
      let R := (C0*Real.exp H*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        ((poolCap s)^2*K*((min 1 (kernelReference (Z^(3*B)) H))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹)
      change _=R
      calc
        _=R*(sourceVolume s*(sourceVolume s)⁻¹) := by
          dsimp only [R,H]
          simp only [Real.rpow_one,massCap,div_eq_mul_inv,mul_inv_rev,mul_pow]
          ring
        _=R := by rw [mul_inv_cancel₀ hv.ne',mul_one]
    _≤(C0*Real.exp H*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        ((1+Real.exp (2*H))^2*Z^(-saving)) := mul_le_mul_of_nonneg_left hn (by positivity)
    _=_ := by ring

private theorem weighted_normalized_sum (Ds : Finset Id) (w : Id→ℝ) (f : Id→ℂ)
    (V W B : ℝ) (hV : 0<V) (hW : 0<W) (hB : 0≤B)
    (hw : ∀F∈Ds,0≤w F) (hf : ∀F∈Ds,‖f F‖/V≤B) :
    ‖∑F∈Ds,(w F:ℂ)*f F‖/(V*W)≤((∑F∈Ds,w F)/W)*B := by
  have hh : ‖∑F∈Ds,(w F:ℂ)*f F‖≤(∑F∈Ds,w F)*(V*B) := by
    calc
      _≤∑F∈Ds,‖(w F:ℂ)*f F‖ := norm_sum_le _ _
      _≤∑F∈Ds,w F*(V*B) := by
        apply Finset.sum_le_sum
        intro F hF
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw F hF)]
        apply mul_le_mul_of_nonneg_left _ (hw F hF)
        simpa only [mul_comm B V] using (div_le_iff₀ hV).mp (hf F hF)
      _=_ := by rw [Finset.sum_mul]
  apply (div_le_div_of_nonneg_right hh (mul_pos hV hW).le).trans_eq
  field_simp [hV.ne',hW.ne']
  <;> ring

/-- The literal selected weighted first tail. The exact selected mass
stays visible; no cancellation or independence of the twists is used. -/
theorem selected_first_tail (N : ℕ) (b B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,Fintype.card ι≤N→
      ∀ha : 0<a,0≤b→∀(seed : Id)(η : Character)(m A : O)(t K W : ℝ)(Φ : 𝓢(ℝ,ℂ)),
      0<K→0<W→poolCap s≤Z^B→sourceVolume s≤Z^B→K≤Z^B→K⁻¹≤Z^B→
      ∀(Ds : Finset Id)(w : Id→ℝ),(∀F∈Ds,0≤w F)→
      ‖∑F∈Ds,(w F:ℂ)*CenteredMomentFirstSectorLocalization.discardedEnergy η m A t
        (sourceColumns s) (selectedCoefficient s ha seed F) Φ K (sourceVolume s) Z ξ‖/
        (sourceVolume s*W)≤
      ((∑F∈Ds,w F)/W)*(C*(profileCap s)^2*
        control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)) := by
  obtain ⟨control,C,hC,hbound⟩ := normalized_first_tail N b B ξ saving hB hξ
  refine ⟨control,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a s hN ha hb seed η m A t K W Φ hK hW hp hV hKc hKic Ds w hw
  apply weighted_normalized_sum Ds w _ (sourceVolume s) W _ (sourceVolume_pos s) hW
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
      (apply_nonneg (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) Φ))
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)) hw
  intro F hF
  exact hZ.2 ι a s hN ha hb seed F η m A t K Φ hK hp hV hKc hKic

theorem selected_first_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,0<b→∀(seed : Id)(η : Character)(m A : O)
      (t K W : ℝ)(Φ : 𝓢(ℝ,ℂ)),0≤K→0<W→
      ∀(Ds : Finset Id)(w : Id→ℝ),(∀F∈Ds,0≤w F)→
      ‖∑F∈Ds,(w F:ℂ)*zeroEnergy η m A t
        (sourceColumns s) (selectedCoefficient s ha seed F) Φ K‖/(sourceVolume s*W)≤
      ((∑F∈Ds,w F)/W)*(C*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*
        (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε) := by
  obtain ⟨C,hC,hbound⟩ := normalized_first_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι instι a b s hN ha hb seed η m A t K W Φ hK hW Ds w hw
  apply weighted_normalized_sum Ds w _ (sourceVolume s) W _ (sourceVolume_pos s) hW
    (mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (sq_nonneg _)) (norm_nonneg _))
        (div_nonneg (mul_nonneg (sq_nonneg b) (pow_nonneg (by norm_num) _))
          (pairNorm_pos s.hd.1 s.hd.2).le))
      (Real.rpow_nonneg (source_cap_nonneg s) _)) hw
  intro F hF
  exact hbound ι a b s hN ha hb seed F η m A t K Φ hK

/-- Concrete finite selected mass: original prime-product padding is
retained once. The tuple multiplicity is represented by the actual
weight bound L, rather than an unjustified product injectivity claim. -/
theorem actual_selected_mass {α : Type v} [Fintype α]
    (q : MixedSupplierFourthRow.Data α) (hP : ∀i,0<q.P i)
    (hpool : ∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)
    (w : Id→ℝ) (L : ℝ) (hL : 0≤L)
    (hw : ∀F∈MixedSupplierPositive.selectedProducts q,0≤w F∧w F≤L) :
    (∑F∈MixedSupplierPositive.selectedProducts q,w F)/MixedSelectedVolume.volume q≤
      128*MixedSelectedVolume.padding q*L := by
  have hscale := MixedSelectedVolume.scale_pos q hP
  have hvol := MixedSelectedVolume.volume_pos q hP
  have hsub : MixedSupplierPositive.selectedProducts q⊆idealBall (MixedSelectedVolume.scale q) := by
    intro F hF
    exact (mem_idealBall _ _).mpr
      ⟨(MixedSupplierPositive.selected_products_supported q F hF).1,
        MixedSelectedVolume.selected_products_norm q hpool F hF⟩
  have hc : ((MixedSupplierPositive.selectedProducts q).card:ℝ)≤
      ((idealBall (MixedSelectedVolume.scale q)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcard : ((MixedSupplierPositive.selectedProducts q).card:ℝ)≤128*MixedSelectedVolume.scale q :=
    hc.trans (idealBall_card _ hscale.le)
  have hsum : (∑F∈MixedSupplierPositive.selectedProducts q,w F)≤
      128*MixedSelectedVolume.scale q*L := by
    calc
      _≤∑_F∈MixedSupplierPositive.selectedProducts q,L := Finset.sum_le_sum (fun F hF=>(hw F hF).2)
      _=((MixedSupplierPositive.selectedProducts q).card:ℝ)*L := by rw [Finset.sum_const,nsmul_eq_mul]
      _≤_ := mul_le_mul_of_nonneg_right hcard hL
  apply (div_le_div_of_nonneg_right hsum hvol.le).trans_eq
  unfold MixedSelectedVolume.scale
  field_simp [hvol.ne']
  <;> ring

end
end Candidate.SilPrior.FourthPower.MixedFirstRemainder
