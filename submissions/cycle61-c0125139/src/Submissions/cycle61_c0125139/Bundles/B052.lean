/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B046
import Submissions.cycle61_c0125139.Bundles.B051
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformRetainedEnergy

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorPacketMellin; sha256 6e01f732f9e73496113f84a10556a91fbd052ea4d6a7f24868964f58af20b5a9 -/
section
                                                      
                                                      

/-! Mellin inversion of the actual numerator with the complete error packet. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

instance correctionIndex_countable (S : Finset (Ideal O)) (u : FreeRow) :
    Countable (CorrectionIndex S u) := by unfold CorrectionIndex EulerIndex; infer_instance
instance errorPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) : Countable (ErrorPacketIndex S u T) := by
  unfold ErrorPacketIndex
  infer_instance

theorem error_packet_central_summable (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (x z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hmargin : 1 + firsteps ≤ x.re + 1 / 2) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ))) := by
  have hC := (continuedCorrection_coefficient_mass firsteps (1 / 2)
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx hz (by norm_num) hmargin).1
  have hE := (hasSum_fintype (fun j : T → Fin 4 => ‖errorTupleCoefficient η u T hT x z j‖ *
    (errorTupleScale T j : ℝ)^(-(1 / 2 : ℝ)))).summable
  exact weighted_product_summable _ _ _ _ (1 / 2) hE hC

theorem actual_error_packet_mellin (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hmargin : 1 + firsteps ≤ x.re + 1 / 2)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0 < Y) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
      (Y : ℂ)^(((1 / 2 : ℂ) + t * I) - 1) * mellin W ((1 / 2 : ℂ) + t * I) *
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1 / 2 : ℂ) + t * I) *
      ((∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x ((1 / 2 : ℂ) + t * I) z) *
        continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T)
          η u x ((1 / 2 : ℂ) + t * I) z)) =
    (Y : ℂ)^(-(1 / 2 : ℂ)) * ∑' e : ErrorPacketIndex S u T,
      errorPacketCoefficient S hS η u T hT x z e *
        (errorPacketScale S u T e : ℂ)^(-(1 / 2 : ℂ)) *
        HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
          (Y / (errorPacketScale S u T e : ℝ)) 0 0 := by
  have he (t : ℝ) := error_packet_expansion S hS firsteps hfirst η u T hT hη
    x ((1 / 2 : ℂ) + t * I) z hQ hx hz
    (by simp; norm_num) (by simpa using hmargin)
  simp_rw [he]
  exact MellinReconstruction.weighted_numerator_mellin (rowCharacter S hS.prime u) hrow
    W a b ha hsupp hW Y hY
    (errorPacketCoefficient S hS η u T hT x z) (fun e => (errorPacketScale S u T e : ℝ))
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e))
    (error_packet_central_summable S hS firsteps hfirst η u T hT x z hx hz hmargin)

theorem reconstructed_numerator_bound {κ : Type*} [Countable κ]
    (χ : Character) (W : ℝ → ℂ) (a b Y L rho M B : ℝ)
    (hsupp : Function.support W ⊆ Icc a b) (hY : 0 < Y) (hM : 0 ≤ M)
    (A : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (hmass : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho))
    (hmb : (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ≤ B)
    (hpoly : ∀ i, N i ≤ b * Y → ‖HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * max 1 (L * N i)^rho) :
    ‖(Y : ℂ)^(-(1 / 2 : ℂ)) * ∑' i,
      A i * (N i : ℂ)^(-(1 / 2 : ℂ)) * HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
        Y^(-(1 / 2 : ℝ)) * (M * B) := by
  have hpoly' (i : κ) : ‖HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * max 1 (L * N i)^rho := by
    by_cases hi : N i ≤ b * Y
    · exact hpoly i hi
    · rw [MellinReconstruction.polynomial_zero_of_scale_cutoff χ W a b Y (N i)
        hsupp hY (hN i) (lt_of_not_ge hi),norm_zero]
      exact mul_nonneg hM (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) rho)
  have hbound (i : κ) :
      ‖A i * (N i : ℂ)^(-(1 / 2 : ℂ)) * HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * (‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i)]
    rw [show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
    calc
      _ ≤ (‖A i‖ * (N i)^(-(1 / 2 : ℝ))) * (M * max 1 (L * N i)^rho) :=
        mul_le_mul_of_nonneg_left (hpoly' i) (by have := hN i; positivity)
      _ = _ := by ring
  have hs := (hmass.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hn := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hbound (hmass.mul_left M))
  rw [tsum_mul_left] at hn
  have hm := hn.trans (mul_le_mul_of_nonneg_left hmb hM)
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
  rw [show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hY.le _)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorPacketMellin -/

/- BEGIN ORIGINAL Cycle25.Numerator.ReflectionMass; sha256 6a9da020c2299b96a4bc868667b1b7c0f9b545ad758a7b9ba3e898fed814fd59 -/
section
                                                                   

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25WeightedNumeratorReflection
open HeckeFamily CenteredMomentReflectionWeightedEnergy

/-- Row-dependent absolutely summable coefficient packets preserve a fourth moment
when every independent rowwise choice has that fourth moment. -/
theorem weighted_fourth_selection {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀i, α i) (w f : ∀i, α i → ℂ) (M E : ℝ) (_hM : 0 ≤ M)
    (hs : ∀i, Summable (fun a => ‖w i a‖))
    (hm : ∀i, (∑'a, ‖w i a‖) ≤ M)
    (hselection : ∀a : ∀i, α i, (∑i, ‖f i (a i)‖^4) ≤ E) :
    (∀i, Summable (fun a => ‖w i a*f i a‖)) ∧
      (∑i, ‖∑'a, w i a*f i a‖^4) ≤ M^4*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  have hpoint (i : ι) (a : α i) : ‖f i a‖^4 ≤ E := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j => ‖f j (Function.update base i a j)‖^4)
      (fun j _ => by positivity) (Finset.mem_univ i)
    exact (by simpa using hh : ‖f i a‖^4 ≤ ∑j, ‖f j (Function.update base i a j)‖^4).trans
      (hselection (Function.update base i a))
  let v (i : ι) : ℝ := ⨆a, ‖f i a‖^4
  have hbd (i : ι) : BddAbove (Set.range (fun a => ‖f i a‖^4)) :=
    ⟨E, by rintro _ ⟨a,rfl⟩; exact hpoint i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^4 ≤ v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0 ≤ v i := (by positivity : 0 ≤ ‖f i (base i)‖^4).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖ ≤ Real.sqrt (Real.sqrt (v i)) := by
    apply (Real.le_sqrt (norm_nonneg _) (Real.sqrt_nonneg _)).mpr
    apply (Real.le_sqrt (sq_nonneg _) (hv0 i)).mpr
    convert hv i a using 1 <;> ring
  have hw (i : ι) : Summable (fun a => ‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (Real.sqrt (v i)))).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a, w i a*f i a‖ ≤ M*Real.sqrt (Real.sqrt (v i)) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (Real.sqrt (v i))))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  have hroot (i : ι) : (Real.sqrt (Real.sqrt (v i)))^4 = v i := by
    calc
      _ = ((Real.sqrt (Real.sqrt (v i)))^2)^2 := by ring
      _ = v i := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (hv0 i)]
  refine ⟨hw,?_⟩
  calc
    (∑i, ‖∑'a, w i a*f i a‖^4) ≤ ∑i, (M*Real.sqrt (Real.sqrt (v i)))^4 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hsum i) 4)
    _ = M^4*∑i, v i := by simp only [mul_pow,hroot,Finset.mul_sum]
    _ ≤ M^4*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a => ‖f i a‖^4) E hselection) (by positivity)

/-- The natural primitive restoration and annular weights have only a subpower cost
for fourth moments, including an arbitrary row-dependent mask of norm at most one. -/
theorem actual_masked_reflection_fourth (ε : ℝ) (hε : 0 < ε) :
    ∃C : ℝ, 0 < C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι → Finset (Ideal HeckeFamily.O)), (∀i P, P ∈ S i → Prime P) →
      ∀(η ηi : ι → Character) (B : ι → ℕ), (∀i, 2 ≤ B i) →
      ∀R E : ℝ, 1 ≤ R → (∀i, (Ideal.absNorm (∏P∈S i,P):ℝ) ≤ R) →
      ∀(mask f : ∀i, Index (S i) → ℂ), (∀i a, ‖mask i a‖ ≤ 1) →
      (∀a : ∀i, Index (S i), (∑i, ‖f i (a i)‖^4) ≤ E) →
      (∀i, Summable (fun a => ‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i, ‖∑'a, (mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^4)
        ≤ C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/4) (by positivity)
  refine ⟨C^4,by positivity,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0 ≤ R := by linarith
  let M := C*R^(ε/4)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a, ‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖) ≤ M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0 ≤ ε/4)) hC.le
  have hh := weighted_fourth_selection (fun i => baseIndex (S i))
    (fun i a => mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/4))^4 = R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

end SevenEighths.Cycle25WeightedNumeratorReflection
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.ReflectionMass -/

/- BEGIN ORIGINAL Cycle25.Numerator.ReflectionProfiles; sha256 6e542569e1f31b0fe93abf136c1886211070efe4f047a7b0ba072b9cb713f204 -/
section
                                                                   
                                                                   
                                                                 
                                                                 

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentOneReflectionScaleEnergy
open CenteredMomentUniformReflectionProfile CenteredMomentReflectedProfileMeasure
open CenteredMomentFrequencyScaleSupremum CenteredMomentScaleSupremum
open CenteredMomentReflectedNormalization CenteredMomentSectorLocalization

/-- Applying the actual Fourier separation theorem twice transports a fourth moment,
with selected prime factors still squared. Profiles and scales may depend on the row. -/
theorem reflected_fourth_profiles (V : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hV : ∀y, V y ≠ 0 → |y| ≤ M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ : ι → Character) (P : ι → ℂ) (s X : ι → ℝ),
      (∀i, 0 < s i) → (∀i, 0 < X i) → ∀D E : ℝ, 0 < D → 0 ≤ E →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      (∀v w : ℝ,
        (∑i, ‖polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v) *
          polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E * ((1+‖v‖)^J)^2 * ((1+‖w‖)^J)^2) →
      (∑i, ‖polynomial (χ i) false
        (fun x => logWindow V x * ((1+s i)^A:ℂ) * paperRadialFourier (G i) (s i*x))
          (X i) 0 0‖^4 * ‖P i‖^2) ≤ C*D^4*E := by
  obtain ⟨H,K,hK,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,K^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  let f (i : ι) : ℂ := polynomial (χ i) false
    (fun x => logWindow V x * ((1+s i)^A:ℂ) * paperRadialFourier (G i) (s i*x))
      (X i) 0 0
  let p (i : ι) (v : ℝ) : ℂ :=
    polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)
  have hinner (v : ℝ) :
      (∑i, ‖p i v * f i * P i‖^2) ≤ K*D^2*(E*((1+‖v‖)^J)^2) := by
    have hh := hbound G χ (fun i => p i v * P i) s X hs hX D
      (E*((1+‖v‖)^J)^2) hD (by positivity) hGD (by
        intro w
        have he : (∑i, ‖p i w * (p i v * P i)‖^2) =
            ∑i, ‖p i v * p i w * P i‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          congr 2
          ring
        change (∑i, ‖p i w * (p i v * P i)‖^2) ≤ _
        rw [he]
        exact henergy v w)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring
  have houter := hbound G χ (fun i => f i * P i) s X hs hX D
    (K*D^2*E) hD (by positivity) hGD (by
      intro v
      have he : (∑i, ‖p i v * (f i * P i)‖^2) = ∑i, ‖p i v * f i * P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc]
      change (∑i, ‖p i v * (f i * P i)‖^2) ≤ _
      rw [he]
      exact (hinner v).trans_eq (by ring))
  calc
    _ = ∑i, ‖f i * (f i * P i)‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [f,norm_mul]
      ring
    _ ≤ K*D^2*(K*D^2*E) := houter
    _ = _ := by ring

/-- The two scale-supremum variables remove row-dependent reflected lengths.
This is an actual fourth-moment statement about Hecke polynomials. -/
theorem reflected_fourth_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ : ι → Character) (P : ι → ℂ)
        (s X : ι → ℝ) (lo hi D E : ℝ),
      lo ≤ hi → (∀i, 0 < s i) → (∀i, 0 < X i) →
      (∀i, Real.log (X i) ∈ Set.Icc lo hi) → 0 < D → 0 ≤ E →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      (∀v w : ℝ, ∀j k : Fin 2, ∀x ∈ Set.Icc lo hi, ∀y ∈ Set.Icc lo hi,
        (∑i, ‖polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E * ((1+‖v‖)^J)^2 * ((1+‖w‖)^J)^2) →
      (∑i, ‖polynomial (χ i) false
        (fun x => (annulus x:ℂ) * ((1+s i)^A:ℂ) * paperRadialFourier (G i) (s i*x))
          (X i) 0 0‖^4 * ‖P i‖^2) ≤ C*D^4*(1+2*(hi-lo))^2*E := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y, CenteredMomentReflectedAnnuli.logWindow y ≠ 0 → |y| ≤ Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨H,C,hC,hbound⟩ := reflected_fourth_profiles
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X lo hi D E hlh hs hX hlogX hD hE hGD henergy
  have hlength : 0 ≤ 1+2*(hi-lo) := by linarith
  have hfixed (v w : ℝ) :
      (∑i, ‖polynomial (χ i) false (logWindow CenteredMomentReflectedAnnuli.logWindow)
        (X i) 0 (2*Real.pi*v) *
        polynomial (χ i) false (logWindow CenteredMomentReflectedAnnuli.logWindow)
        (X i) 0 (2*Real.pi*w) * P i‖^2)
      ≤ ((1+2*(hi-lo))^2*E) * ((1+‖v‖)^J)^2 * ((1+‖w‖)^J)^2 := by
    have hh := paired_rowwise_scales Finset.univ χ χ (fun _ => 2*Real.pi*v)
      (fun _ => 2*Real.pi*w) P (fun z : ℝ => (annulus z:ℂ))
      (fun z : ℝ => (annulus z:ℂ)) (1/4) 1 (1/4) 1 (by norm_num) (by norm_num)
      annulus_complex_support annulus_complex_support annulus_complex_smooth annulus_complex_smooth
      lo hi lo hi (E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2) hlh hlh
      (fun i => Real.log (X i)) (fun i => Real.log (X i))
      (fun i _ => hlogX i) (fun i _ => hlogX i) (henergy v w)
    simp only [Real.exp_log (hX _)] at hh
    rw [actual_log_window]
    exact hh.trans_eq (by ring)
  have hh := hbound G χ P s X hs hX D ((1+2*(hi-lo))^2*E)
    hD (by positivity) hGD hfixed
  simp only [actual_log_window] at hh
  exact hh.trans_eq (by ring)

end SevenEighths.Cycle25WeightedNumeratorReflection
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.ReflectionProfiles -/

/- BEGIN ORIGINAL Cycle25.Numerator.ReflectionRetained; sha256 c4dfd544a778667bc14ae8c0f9d1262e3763a0c136de3577df40e4ea961b6c8f -/
section
                                           
                                       
                                                                

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentRetainedWeightedSource CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentUniformRetainedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_mul_sqrt_fourth (z q : ℂ) :
    ‖z*(Real.sqrt ‖q‖:ℂ)‖^4 = ‖z‖^4*‖q‖^2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  calc
    _ = ((Real.sqrt ‖q‖)^2)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (norm_nonneg _)]

/-- Exact natural primitive restoration, including its summable redundant-prime
and annular packet, transports the rowwise reflected fourth moment. -/
theorem actual_retained_uniform_fourth (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B J : ℕ) (hB : 2 ≤ B) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ ψ : ι → Character) (P : ι → ℂ)
        (X R : ι → ℝ) (lo hi D E Rcap : ℝ),
      (∀i, 0 < X i) → lo ≤ hi →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0 < dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2 ∈ retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) ∈ Set.Icc lo hi) →
      0 < D → 0 ≤ E → (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ) ≤ Rcap) →
      (∀v w : ℝ, ∀j k : Fin 2, ∀x ∈ Set.Icc lo hi, ∀y ∈ Set.Icc lo hi,
        (∑i, ‖polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2) →
      (∑i, ‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)‖^4*‖P i‖^2)
        ≤ C*Rcap^epsilon*D^4*(1+2*(hi-lo))^2*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := reflected_fourth_rowwise_scales B J
  obtain ⟨Cw,hCw,hw⟩ := actual_masked_reflection_fourth epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R lo hi D E Rcap hX hlh hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let keep (i : ι) (u : α i) := u.2 ∈ retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  let c (i : ι) : ℂ := Real.sqrt ‖P i‖
  let f (i : ι) (u : α i) :=
    retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (c i) u
  have hselected (u : ∀i, α i) :
      (∑i, ‖f i (u i)‖^4) ≤ Cp*D^4*(1+2*(hi-lo))^2*E := by
    let Y (i : ι) := if keep i (u i) then
      dyadicScale (u i).2*dualScale (χ i) (ψ i) (X i) (u i).1.1 (u i).1.2
      else Real.exp lo
    let P' (i : ι) := if keep i (u i) then P i else 0
    have hY (i : ι) : 0 < Y i := by
      dsimp [Y]
      split_ifs
      · exact mul_pos (dyadicScale_pos _) (dualScale_pos _ _ _ (hX i) _ _)
      · exact Real.exp_pos _
    have hlogY (i : ι) : Real.log (Y i) ∈ Set.Icc lo hi := by
      dsimp [Y]
      split_ifs with hk
      · exact hgeom i (u i) _ hk
      · simp only [Real.log_exp]; exact ⟨le_rfl,hlh⟩
    have he (v w : ℝ) (j k : Fin 2) (x : ℝ) (hx : x ∈ Set.Icc lo hi)
        (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
        (∑i, ‖polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P' i‖^2)
          ≤ E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
      apply (Finset.sum_le_sum (fun i _ => ?_)).trans (henergy v w j k x hx y hy)
      dsimp only [P']
      split_ifs
      · exact le_rfl
      · simp only [mul_zero,norm_zero,zero_pow (by omega : 2 ≠ 0)]
        exact sq_nonneg _
    have hh := hp G (fun i => (χ i).inverse) P' (fun i => dyadicScale (u i).2)
      Y lo hi D E hlh (fun i => dyadicScale_pos _) hY hlogY hD hE hGD he
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f,retainedColumn]
    simp only [normalized_zero]
    by_cases hk : keep i (u i)
    · simp only [keep] at hk
      rw [if_pos hk]
      dsimp [Y,P',keep,c]
      rw [if_pos hk,if_pos hk,norm_mul_sqrt_fourth]
    · have hk' := hk
      simp only [keep] at hk'
      rw [if_neg hk']
      simp only [norm_zero,zero_pow (by omega : 4 ≠ 0)]
      dsimp [P',keep]
      rw [if_neg hk']
      simp
  have hh := hw (fun i => sourcePrimes (χ i) (ψ i))
    (fun i Q hQ => redundantSet_prime _ _ Q hQ) ψ (fun i => (ψ i).inverse)
    (fun _ => B) (fun _ => hB) Rcap _ hRcap hcap (fun _ _ => 1) f
    (by intro i a; simp) hselected
  simp only [one_mul] at hh
  have hid (i : ι) :
      retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*c i =
      ∑'a, signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) B a*f i a := by
    have he := retainedOriginal_eq_weighted (χ i) (ψ i) (G i) (X i) (R i) 0
      (hX i) B 0 (c i) (hh.1 i)
    simpa only [retained_zero,pow_zero,Complex.ofReal_one,one_mul] using he
  calc
    _ = ∑i, ‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*c i‖^4 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (norm_mul_sqrt_fourth _ (P i)).symm
    _ = ∑i, ‖∑'a, signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) B a*f i a‖^4 := by
      simp_rw [hid]
    _ ≤ Cw*Rcap^epsilon*(Cp*D^4*(1+2*(hi-lo))^2*E) := hh.2
    _ = _ := by ring

end SevenEighths.Cycle25WeightedNumeratorReflection
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.ReflectionRetained -/
