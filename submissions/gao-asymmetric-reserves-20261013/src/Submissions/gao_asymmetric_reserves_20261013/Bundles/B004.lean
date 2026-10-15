/- Asymmetric reserve and endpoint refinement: Zhongpai Gao, with AI assistance. Adapts Kari Roegnvaldsson’s affine/reserve source at 14ab1618c5133a7d12e06aa76661bbcb34e843cd, following accepted c707738a659786b9a44a79c629bed8c801cca8f3. Original notices below are retained. -/
/- Reserve-balanced rational refinement: Zhongpai Gao, with AI assistance.
Builds on Kari Roegnvaldsson's affine-capacity and reserve-allocation source,
nielstron's complete local-moment proof, and retained predecessor notices.
This adaptation enlarges the certified defect to 1/241 and specializes the
linked geometry to 8748673/10000000. Original notices below remain intact. -/
/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Mathlib
import Mathlib.Tactic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeRay
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.Parameters ; sha256 1dba1bb378b2f93b88e833d45fea753ca42ee98ab09bceb93bde31520358d501 -/
section


/-!
Exact real parameters for the weighted physical numerator proof.
No analytic theorem or QRH conclusion is assumed in this module.
-/

namespace Cycle25.Weighted

noncomputable section

def theta : ℝ := 10499 / 12000
def ell : ℝ := 167 / 1000
def b : ℝ := 43 / 500
def lx : ℝ := 747 / 2000
def ly : ℝ := 919 / 2000
def h : ℝ := 1587 / 2000
def kappa : ℝ := 3 / 4
def endpointMargin : ℝ := 1 / 10000
def rowExtension : ℝ := 1 / 1000000
def publicBenchmark : ℝ := 874957019420098946128604623 / 10^27
def signal (s : ℝ) : ℝ := s - (4 + b) / 6

theorem theta_eq : theta = (11 : ℝ) / 12 - ell / 4 := by
  norm_num [theta, ell]

theorem theta_pos : 0 < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7 : ℝ) / 8 := by norm_num [theta]
theorem theta_lt_public : theta < publicBenchmark := by
  norm_num [theta, publicBenchmark]
theorem theta_gt_half : (1 : ℝ) / 2 < theta := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]
theorem kappa_admissible : (1 + kappa) / 2 = (7 : ℝ) / 8 := by
  norm_num [kappa]
theorem endpointMargin_pos : 0 < endpointMargin := by norm_num [endpointMargin]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension]
theorem rowExtension_cost : 2 * rowExtension < endpointMargin / 2 := by
  norm_num [rowExtension, endpointMargin]

theorem length_sum : lx + ly = 1 - ell := by norm_num [lx, ly, ell]
theorem length_difference : ly - lx = b := by norm_num [lx, ly, b]
theorem row_endpoint : h = 1 - lx + ell := by norm_num [h, lx, ell]
theorem signal_low : signal theta = lx / 2 + b / 12 := by
  norm_num [signal, theta, lx, b]
theorem signal_slope (s t : ℝ) : signal s - signal t = s - t := by
  simp only [signal]; ring

theorem b_pos : 0 < b := by norm_num [b]
theorem ell_pos : 0 < ell := by norm_num [ell]
theorem ell_lt_one_fifth : ell < (1 : ℝ) / 5 := by norm_num [ell]
theorem x_rescaled_pos : 0 < lx - ell := by norm_num [lx, ell]
theorem y_rescaled_pos : 0 < ly - ell := by norm_num [ly, ell]
theorem row_rescaled_pos : 0 < 1 - 3 * ell := by norm_num [ell]
theorem gram_domination : 0 < ly - ell - (11 : ℝ) / 6 * b := by
  norm_num [ly, ell, b]
theorem h_pos : 0 < h := by norm_num [h]
theorem h_gt_half : (1 : ℝ) / 2 < h := by norm_num [h]
theorem h_lt_one : h < 1 := by norm_num [h]
theorem row_count_supply : (7 : ℝ) / 37 < ell / h := by norm_num [ell, h]
theorem row_extension_supply : h < 5 * ell := by norm_num [h, ell]
theorem numerator_short : h < 2 * ly := by norm_num [h, ly]
theorem ly_lt_half : ly < (1 : ℝ) / 2 := by norm_num [ly]
theorem numerator_supply : (2 * ly - (1 : ℝ) / 2) / (6 * kappa) < ell := by
  norm_num [ly, kappa, ell]
theorem extended_row_count_supply : (7 : ℝ) / 37 < ell / (h + rowExtension) := by
  norm_num [ell, h, rowExtension]
theorem extended_numerator_short : h + rowExtension < 2 * ly := by
  norm_num [h, rowExtension, ly]
theorem extended_h_lt_one : h + rowExtension < 1 := by norm_num [h, rowExtension]
theorem extended_row_supply : h + rowExtension < 5 * ell := by
  norm_num [h, rowExtension, ell]

theorem numerator_supply_all {d : ℝ} (hd : (1 : ℝ) / 2 ≤ d) :
    (2 * ly - d) / (6 * kappa) < ell := by
  norm_num [ly, kappa, ell] at *
  linarith

theorem numerator_range {d : ℝ} (hd : (1 : ℝ) / 2 ≤ d) (hdh : d ≤ h) :
    d / 2 < ly ∧ ly < d := by
  norm_num [h, ly] at *
  constructor <;> linarith

theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v + max 0 (5 * ell - 1 + v) / 8 ≤ 0 := by
  have hm : max 0 (5 * ell - 1 + v) ≤ 8 * v := by
    apply max_le
    · linarith
    · norm_num [ell]
      linarith
  linarith

theorem low_rescaled_identity (v : ℝ) :
    (1 - ell - 2 * v) + (ell - v) - 1 = -3 * v := by ring

theorem small_row_margin :
    h * ((17 : ℝ) / 50 - 1 / 6) - ly / 2 + 63 / 5000 < 0 := by
  norm_num [h, ly]
theorem principal_w_margin : 0 < ly / 20 := by norm_num [ly]
theorem principal_z_margin : 0 < h / 600 := by norm_num [h]
theorem euler_tail_capacity_gap : (1 : ℝ) / 4 - 1 / (12 * kappa) = 5 / 36 := by
  norm_num [kappa]

theorem principal_local_exponents :
    -(6 : ℝ) * (33 / 200) ≤ -theta ∧
    4 - 5 * theta - 6 * (33 / 200) ≤ -theta ∧
    1 - (19 : ℝ) / 20 - 6 * (33 / 200) ≤ -theta := by
  norm_num [theta]

theorem principal_euler_defects :
    4 - 6 * theta - 6 * ((33 : ℝ) / 200) < -1 ∧
    1 - theta - (19 : ℝ) / 20 - 6 * (33 / 200) < -1 := by
  norm_num [theta]

/-- The exact nonnegative dual identity for the unchanged low estimates. -/
theorem low_barrier_identity (M ℓ e : ℝ) :
    M / 12 - ℓ / 6 + e / 2 - 1 / 30 =
      (1 / 5 : ℝ) * (e - (1 + 3 * ℓ - 2 * M) / 4) +
      (1 / 60 : ℝ) * (e - (M + ℓ - 1)) + (17 / 60 : ℝ) * e := by ring

/-- A limitation of the stated sufficient low-exponent system, not of zeros. -/
theorem low_barrier {B M ℓ e : ℝ}
    (he : 0 ≤ e)
    (henergy₁ : (1 + 3 * ℓ - 2 * M) / 4 ≤ e)
    (henergy₂ : M + ℓ - 1 ≤ e)
    (hlow : (5 : ℝ) / 6 + M / 12 - ℓ / 6 + e / 2 ≤ B) :
    (13 : ℝ) / 15 ≤ B := by
  linarith

/-- The same scoped barrier before eliminating the Gram exponent g. -/
theorem physical_low_barrier {B xLen yLen ℓ g e : ℝ}
    (hg : (yLen - xLen) / 6 ≤ g)
    (he : 0 ≤ e)
    (henergy₁ : (1 + 3 * ℓ - 2 * (xLen + yLen)) / 4 ≤ e)
    (henergy₂ : xLen + yLen + ℓ - 1 ≤ e)
    (hlow : (5 : ℝ) / 6 + xLen / 6 - ℓ / 6 + g / 2 + e / 2 ≤ B) :
    (13 : ℝ) / 15 ≤ B := by
  apply low_barrier he henergy₁ henergy₂
  linarith

end
end Cycle25.Weighted

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.Parameters -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.ReflectionMass ; sha256 6a9da020c2299b96a4bc868667b1b7c0f9b545ad758a7b9ba3e898fed814fd59 -/
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
/- END ORIGINAL MODULE Cycle25.Numerator.ReflectionMass -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.ReflectionProfiles ; sha256 6e542569e1f31b0fe93abf136c1886211070efe4f047a7b0ba072b9cb713f204 -/
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
/- END ORIGINAL MODULE Cycle25.Numerator.ReflectionProfiles -/

/- BEGIN ORIGINAL MODULE Endpoint.Arithmetic ; sha256 617135f93036467b5458db5b9a659a5c9e952bb8fc0ad5d83cf20cb8442738b9 -/
section

noncomputable section
namespace Submission20261012.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 4000
def theta : ℝ := 8748673 / 10000000
def ell : ℝ := 1253981 / 7500000
def h : ℝ := 397 / 500
def y : ℝ := h - 2 * ell
def x : ℝ := 1 + ell - h
def kappa : ℝ := 3748673 / 5000000
def junction : ℝ := h - 1 / 1000
def deltaV (δ : ℝ) : ℝ := 5 / 6 - δ
def denomD (p : ℝ) : ℝ := 3 - p - 2 * p / (3 * kappa)
def slotB (p : ℝ) : ℝ := 2 * (1 - p) * (1 - p / (3 * kappa))
def denomJ (δ p : ℝ) : ℝ := deltaV δ * denomD p + δ * slotB p
def regular (d c δ p : ℝ) : ℝ :=
  1 / 2 + h * (13 / 75) - y / 2 - ell / 2 + (33 / 50) * d
    + δ * (1 / 2 - 3 * d / 4)
    + δ * p * (ell - (2 * y - d) / (2 * c))
def highRowExponent (d c δ p : ℝ) : ℝ :=
  regular d c δ p + 3 * d * δ * slotB p * deltaV δ / (8 * denomJ δ p)
def cleared (d c reserve δ p : ℝ) : ℝ :=
  8 * denomJ δ p * (theta - reserve - regular d c δ p)
    - 3 * d * δ * slotB p * deltaV δ
/-- Local numerator saving retaining the affine 9/2 defect allowance. -/
def localRegular (d δ p : ℝ) : ℝ :=
  1 / 2 + h * (13 / 75) - y / 2 - ell / 2 + (33 / 50) * d
    + δ * (1 / 2 - 3 * d / 4)
    + δ * p * (ell - (2 * y - d + (1 / 241) * d) / 9)
def localHighRowExponent (d δ p : ℝ) : ℝ :=
  localRegular d δ p + 3 * d * δ * slotB p * deltaV δ / (8 * denomJ δ p)
def localCleared (d reserve δ p : ℝ) : ℝ :=
  8 * denomJ δ p * (theta - reserve - localRegular d δ p)
    - 3 * d * δ * slotB p * deltaV δ
lemma quadratic_nonneg (a b c t : ℝ) (ha : 0 < a)
    (hd : b ^ 2 ≤ 4 * a * c) : 0 ≤ a * t ^ 2 + b * t + c := by
  have hid : 4 * a * (a * t ^ 2 + b * t + c) =
      (2 * a * t + b) ^ 2 + (4 * a * c - b ^ 2) := by ring
  have hp : 0 ≤ 4 * a * (a * t ^ 2 + b * t + c) := by
    rw [hid]
    exact add_nonneg (sq_nonneg _) (sub_nonneg.mpr hd)
  exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*a)).mp hp
lemma denomD_pos (p : ℝ) (hp : p ≤ 1 / 2) : 0 < denomD p := by
  norm_num [denomD, kappa]
  nlinarith
lemma slotB_nonneg (p : ℝ) (hp : p ≤ 1 / 2) : 0 ≤ slotB p := by
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ 1 - p / (3 * kappa) := by
    norm_num [kappa]
    nlinarith
  exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
lemma denomJ_pos (δ p : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp : p ≤ 1 / 2) : 0 < denomJ δ p := by
  have hv : 0 < deltaV δ := by unfold deltaV; linarith
  exact add_pos_of_pos_of_nonneg (mul_pos hv (denomD_pos p hp))
    (mul_nonneg hδ0 (slotB_nonneg p hp))
lemma bound_of_cleared (d c reserve δ p : ℝ)
    (hj : 0 < denomJ δ p) (hc : 0 ≤ cleared d c reserve δ p) :
    highRowExponent d c δ p ≤ theta - reserve := by
  have hd : 0 < 8 * denomJ δ p := by positivity
  have hn : 3 * d * δ * slotB p * deltaV δ ≤
      (theta - reserve - regular d c δ p) * (8 * denomJ δ p) := by
    unfold cleared at hc
    nlinarith
  have hdiv := (div_le_iff₀ hd).mpr hn
  unfold highRowExponent
  linarith

lemma bound_of_local_cleared (d reserve δ p : ℝ)
    (hj : 0 < denomJ δ p) (hc : 0 ≤ localCleared d reserve δ p) :
    localHighRowExponent d δ p ≤ theta - reserve := by
  have hd : 0 < 8 * denomJ δ p := by positivity
  have hn : 3 * d * δ * slotB p * deltaV δ ≤
      (theta - reserve - localRegular d δ p) * (8 * denomJ δ p) := by
    unfold localCleared at hc
    nlinarith
  have hdiv := (div_le_iff₀ hd).mpr hn
  unfold localHighRowExponent
  linarith

def topPolynomial (δ u : ℝ) : ℝ :=
  ((151647901795969961 / 91472307041250000 : ℝ) * δ ^ 2 + (-853292354501176433 / 548833842247500000 : ℝ) * δ + (1229785249133 / 3373805700000 : ℝ)) + u * ((4088049172584307 / 1270448708906250 : ℝ) * δ ^ 2 + (-221072274323974837 / 137208460561875000 : ℝ) * δ + (2825869249133 / 8434514250000 : ℝ))
    + u ^ 2 * ((6070388198999443 / 2540897417812500 : ℝ) * δ ^ 2 + (9608239909994987 / 27441692112375000 : ℝ) * δ + (0 / 1 : ℝ)) + u ^ 3 * ((79603599136 / 73177845633 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ))

lemma topPolynomial_nonneg (δ u : ℝ) (hδ : 0 ≤ δ) (hu : 0 ≤ u) :
    0 ≤ topPolynomial δ u := by
  have h0 : 0 ≤ (151647901795969961 / 91472307041250000 : ℝ) * δ ^ 2 + (-853292354501176433 / 548833842247500000 : ℝ) * δ + (1229785249133 / 3373805700000 : ℝ) :=
    quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h1 : 0 ≤ (4088049172584307 / 1270448708906250 : ℝ) * δ ^ 2 + (-221072274323974837 / 137208460561875000 : ℝ) * δ + (2825869249133 / 8434514250000 : ℝ) :=
    quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h2 : 0 ≤ (6070388198999443 / 2540897417812500 : ℝ) * δ ^ 2 + (9608239909994987 / 27441692112375000 : ℝ) * δ + (0 / 1 : ℝ) :=
    by positivity
  have h3 : 0 ≤ (79603599136 / 73177845633 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ) :=
    by positivity
  unfold topPolynomial
  exact add_nonneg
    (add_nonneg (add_nonneg h0 (mul_nonneg hu h1)) (mul_nonneg (sq_nonneg u) h2))
    (mul_nonneg (pow_nonneg hu 3) h3)
lemma top_identity (δ u : ℝ) :
    localCleared h (1 / 2000000 : ℝ) δ (1 / 2 - u) = topPolynomial δ u := by
  norm_num [localCleared, localRegular, denomJ, deltaV, denomD, slotB, theta, ell,
    h, y, kappa, junction, topPolynomial]
  <;> ring
theorem top_endpoint (δ p : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    localHighRowExponent h δ p ≤ theta - (1 / 2000000 : ℝ) := by
  apply bound_of_local_cleared _ _ _ _ (denomJ_pos δ p hδ0 hδ1 hp1)
  have hu : 0 ≤ 1 / 2 - p := by linarith
  have hid := top_identity δ (1 / 2 - p)
  have hp : (1 / 2 : ℝ) - (1 / 2 - p) = p := by ring
  rw [hp] at hid
  rw [hid]
  exact topPolynomial_nonneg δ (1 / 2 - p) hδ0 hu

def junctionPolynomial (δ u : ℝ) : ℝ :=
  ((789412478011394582923 / 474273537556353750000 : ℝ) * δ ^ 2 + (-2234556642228235773959 / 1422820612669061250000 : ℝ) * δ + (2511394434761 / 6747611400000 : ℝ)) + u * ((10567303754590893638 / 3293566233030234375 : ℝ) * δ ^ 2 + (-2295454327639559799049 / 1422820612669061250000 : ℝ) * δ + (5770822434761 / 16869028500000 : ℝ))
    + u ^ 2 * ((31360047902809008349 / 13174264932120937500 : ℝ) * δ ^ 2 + (51149219291605075141 / 142282061266906125000 : ℝ) * δ + (0 / 1 : ℝ)) + u ^ 3 * ((413410372852448 / 379418830045083 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ))

lemma junctionPolynomial_nonneg (δ u : ℝ) (hδ : 0 ≤ δ) (hu : 0 ≤ u) :
    0 ≤ junctionPolynomial δ u := by
  have h0 : 0 ≤ (789412478011394582923 / 474273537556353750000 : ℝ) * δ ^ 2 + (-2234556642228235773959 / 1422820612669061250000 : ℝ) * δ + (2511394434761 / 6747611400000 : ℝ) :=
    quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h1 : 0 ≤ (10567303754590893638 / 3293566233030234375 : ℝ) * δ ^ 2 + (-2295454327639559799049 / 1422820612669061250000 : ℝ) * δ + (5770822434761 / 16869028500000 : ℝ) :=
    quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h2 : 0 ≤ (31360047902809008349 / 13174264932120937500 : ℝ) * δ ^ 2 + (51149219291605075141 / 142282061266906125000 : ℝ) * δ + (0 / 1 : ℝ) :=
    by positivity
  have h3 : 0 ≤ (413410372852448 / 379418830045083 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ) :=
    by positivity
  unfold junctionPolynomial
  exact add_nonneg
    (add_nonneg (add_nonneg h0 (mul_nonneg hu h1)) (mul_nonneg (sq_nonneg u) h2))
    (mul_nonneg (pow_nonneg hu 3) h3)
lemma junction_identity (δ u : ℝ) :
    cleared junction (6 * kappa) (1 / 10000 : ℝ) δ (1 / 2 - u) = junctionPolynomial δ u := by
  norm_num [cleared, regular, denomJ, deltaV, denomD, slotB, theta, ell,
    h, y, kappa, junction, junctionPolynomial]
  <;> ring
theorem junction_endpoint (δ p : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    highRowExponent junction (6 * kappa) δ p ≤ theta - (1 / 10000 : ℝ) := by
  apply bound_of_cleared _ _ _ _ _ (denomJ_pos δ p hδ0 hδ1 hp1)
  have hu : 0 ≤ 1 / 2 - p := by linarith
  have hid := junction_identity δ (1 / 2 - p)
  have hp : (1 / 2 : ℝ) - (1 / 2 - p) = p := by ring
  rw [hp] at hid
  rw [hid]
  exact junctionPolynomial_nonneg δ (1 / 2 - p) hδ0 hu

def halfPolynomial (δ u : ℝ) : ℝ :=
  ((1451571281391714475423 / 474273537556353750000 : ℝ) * δ ^ 2 + (-8059333726699942534259 / 1422820612669061250000 : ℝ) * δ + (19475990095961 / 6747611400000 : ℝ)) + u * ((10559233371013179151 / 6587132466060468750 : ℝ) * δ ^ 2 + (-4260684104297404933849 / 1422820612669061250000 : ℝ) * δ + (44753018095961 / 16869028500000 : ℝ))
    + u ^ 2 * ((1614385746559008349 / 13174264932120937500 : ℝ) * δ ^ 2 + (271171047123655075141 / 142282061266906125000 : ℝ) * δ + (0 / 1 : ℝ)) + u ^ 3 * ((325510372852448 / 379418830045083 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ))

lemma halfPolynomial_nonneg (δ u : ℝ) (hδ : 0 ≤ δ) (hu : 0 ≤ u) :
    0 ≤ halfPolynomial δ u := by
  have h0 : 0 ≤ (1451571281391714475423 / 474273537556353750000 : ℝ) * δ ^ 2 + (-8059333726699942534259 / 1422820612669061250000 : ℝ) * δ + (19475990095961 / 6747611400000 : ℝ) :=
    quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h1 : 0 ≤ (10559233371013179151 / 6587132466060468750 : ℝ) * δ ^ 2 + (-4260684104297404933849 / 1422820612669061250000 : ℝ) * δ + (44753018095961 / 16869028500000 : ℝ) :=
    quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h2 : 0 ≤ (1614385746559008349 / 13174264932120937500 : ℝ) * δ ^ 2 + (271171047123655075141 / 142282061266906125000 : ℝ) * δ + (0 / 1 : ℝ) :=
    by positivity
  have h3 : 0 ≤ (325510372852448 / 379418830045083 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ) :=
    by positivity
  unfold halfPolynomial
  exact add_nonneg
    (add_nonneg (add_nonneg h0 (mul_nonneg hu h1)) (mul_nonneg (sq_nonneg u) h2))
    (mul_nonneg (pow_nonneg hu 3) h3)
lemma half_identity (δ u : ℝ) :
    cleared (1 / 2) (6 * kappa) (1 / 100 : ℝ) δ (1 / 2 - u) = halfPolynomial δ u := by
  norm_num [cleared, regular, denomJ, deltaV, denomD, slotB, theta, ell,
    h, y, kappa, junction, halfPolynomial]
  <;> ring
theorem half_endpoint (δ p : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    highRowExponent (1 / 2) (6 * kappa) δ p ≤ theta - (1 / 100 : ℝ) := by
  apply bound_of_cleared _ _ _ _ _ (denomJ_pos δ p hδ0 hδ1 hp1)
  have hu : 0 ≤ 1 / 2 - p := by linarith
  have hid := half_identity δ (1 / 2 - p)
  have hp : (1 / 2 : ℝ) - (1 / 2 - p) = p := by ring
  rw [hp] at hid
  rw [hid]
  exact halfPolynomial_nonneg δ (1 / 2 - p) hδ0 hu

theorem geometry :
    theta = 11 / 12 - ell / 4 ∧ kappa = 2 * theta - 1 ∧
    0 < ell ∧ ell < x ∧ x < y ∧ y < 2 * x ∧
    x + y + ell = 1 ∧ y < 1 / 2 ∧ 1 / 2 < h ∧ h < 2 * y ∧
    y - 2 * x + ell < 0 ∧ 1 + 3 * ell - 2 * (x + y) < 0 := by
  norm_num [theta, ell, h, x, y, kappa]
theorem local_window (d : ℝ) (hlo : junction ≤ d)
    (hhi : d ≤ h + 1 / 10000000000) :
    419 / 1000 < 1 - y / d ∧ 1 - y / d < 422 / 1000 := by
  have hd : 0 < d := by
    norm_num [junction, h] at hlo
    linarith
  constructor
  · have hy : y < (1 - 419 / 1000 : ℝ) * d := by
      norm_num [y, h, ell, junction] at *
      nlinarith
    have hv : y / d < (1 - 419 / 1000 : ℝ) := (div_lt_iff₀ hd).2 hy
    linarith
  · have hy : (1 - 422 / 1000 : ℝ) * d < y := by
      norm_num [y, h, ell] at *
      nlinarith
    have hv : (1 - 422 / 1000 : ℝ) < y / d := (lt_div_iff₀ hd).2 hy
    linarith
theorem remaining_scalar_margins :
    h * (13 / 75) - y / 2 + (63 / 50) * (1 / 200) < -(1 / 20) ∧
    (7 / 8 : ℝ) - (49 / 150) * h + (7 / 8) * ell +
      (33 / 50) * (1 / 200) < theta - 1 / 10 ∧
    (51 / 100 : ℝ) + h / 3 + (51 / 100) * ell +
      2 / 10000000000 < theta - 1 / 100 ∧
    ell / (h + 1 / 10000000000) > 4 / 21 ∧
    y < (22 / 5) * ell ∧
    (1 / 2000000 : ℝ) - 2 / 10000000000 > 1 / 3000000 := by
  norm_num [h, y, ell, theta]
end Submission20261012.Endpoint
#print axioms Submission20261012.Endpoint.top_endpoint
#print axioms Submission20261012.Endpoint.junction_endpoint
#print axioms Submission20261012.Endpoint.half_endpoint
#print axioms Submission20261012.Endpoint.geometry
#print axioms Submission20261012.Endpoint.local_window
#print axioms Submission20261012.Endpoint.remaining_scalar_margins
end
/- END ORIGINAL MODULE Endpoint.Arithmetic -/

/- BEGIN ORIGINAL MODULE LocalMoment.BufferedSlot ; sha256 51b4542f41559a4b5c05dae3f5aa387cd42f8e2759545add636134e72a612ed0 -/
section



/-! Buffered pointwise payment for the literal natural prime slots.  The
additional common puncture remains inside the actual row character. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The existing buffered prime estimate pays a genuine natural relative
slot at the local bin parameter `2*a-1`.  The original puncture, zero
extensions, real norm power, and the independent two frequency parameters
are retained exactly. -/
theorem natural_relative_slot_buffered_bound
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8 * e * Rwidth + κ ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax →
      2 ≤ Z ^ d → 2 < Z ^ τ →
      ∀ (ηrow : Character) (z : O) (F : NaturalRow ηrow z)
        (η₀ : Character) (puncture : Ideal O), puncture ≠ 0 →
      let χ := (excluded F.character puncture).product η₀.inverse
      ∀ (hχ : ∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).residue ≠ 1) (a : ℝ) (i : ℕ),
        51 / 100 ≤ a → a ≤ 1 →
        HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e →
      ∀ r σ t v : ℝ, 0 ≤ r → r ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        2 * (|Real.log A| + |Real.log B|) + 1 ≤ Real.log ((Z ^ d) ^ r) →
        (∀ θ : RayQuotient.Characters M H,
          (twistedFamily M H hH χ θ).modulus.absNorm ≤ Z ^ d) →
        |t + v| + Z ^ τ / 2 ≤ (3 * i + 2 : ℕ) * Z ^ τ →
        (3 + (3 * i + 2 : ℕ) * Z ^ τ) ^ 2 ≤ (Z ^ d) ^ η →
        ‖normalizedSlot ηrow (fixedBadMask * idealGenerator puncture) 1 z
          (primePool M H B ((Z ^ d) ^ r))
          (fun I => idealCoeff η₀.inverse I *
            annularWeight W ((Z ^ d) ^ r) σ v I) t ((Z ^ d) ^ r)‖ ^ 2 ≤
          C ^ 2 * (Z ^ d) ^ ((2 * a - 1) * r + 2 * ε) := by
  obtain ⟨C, hC, hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax hRw hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C, hC, ?_⟩
  intro Z d hZ hd hd' hbase hT ηrow z F η₀ puncture hpuncture
    χ hχ a i ha ha' hmax r σ t v hr hr' hσ hσ' hlarge hmod hfreq hheight
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hbasep : 0 < Z ^ d := Real.rpow_pos_of_pos hZp d
  have hscale : 0 < (Z ^ d) ^ r := Real.rpow_pos_of_pos hbasep r
  have hb := hbound Z d hZ hd hd' hbase hT χ hχ a i ha ha' hmax
    r σ (t + v) hr hr' hσ hσ' hlarge hmod hfreq hheight
  rw [relative_normalizedSlot_eq_ray M H ηrow (excluded F.character puncture)
    η₀.inverse (fixedBadMask * idealGenerator puncture) 1 z
    (by simpa only [one_mul] using F.masked_element puncture hpuncture)
    W B ((Z ^ d) ^ r) σ t v hscale, norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power ((Z ^ d) ^ r) t hscale, one_mul]
  apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
  rw [mul_pow, pow_two ((Z ^ d) ^ ((a - 1 / 2) * r + ε)),
    ← Real.rpow_add hbasep]
  congr 2
  ring

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.BufferedSlot -/

/- BEGIN ORIGINAL MODULE LocalMoment.FiniteDeletionBins ; sha256 e6d42d5b92afdfb9b7e27948701c630e747cd96889fbe1b7e0745421963272af -/
section



/-! Exact zero-bin transport through retained finite Euler holes.  This
interface compares zeros, rather than asserting equality of the two
imprimitive L-functions. -/

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDetectorZeros HeckeFiniteDeletion

/-- A retained Euler puncture has no zeros on the positive half-plane.
Both directions include the point `s = 1`, since the actual row is
nonprincipal. -/
theorem positive_zeros_eq_of_mask (χ ψ : Character)
    (hχ : χ.residue ≠ 1)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = 0 ↔ LFunction ψ s = 0 := by
  rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

/-- Inclusion of the positive-real zero sets is enough to compare the
buffered detector maximum; equality of the L-functions is unnecessary. -/
theorem zeroMaximum_le_of_zero_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → Character) (ψ : κ → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ j, (ψ j).residue ≠ 1) (T : ℝ)
    (hinclude : ∀ i, ∃ j, ∀ s : ℂ, 0 < s.re →
      LFunction (χ i) s = 0 → LFunction (ψ j) s = 0) :
    zeroMaximum χ hχ T ≤ zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51 / 100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i, s, hz, ht, hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j, hj⟩ := hinclude i
    rw [← hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · exact hj s (by rw [hs]; linarith) hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

/-- Every retained finite Euler puncture preserves the complete buffered
bin of a finite row-character family, including its baseline and boundary. -/
theorem zeroMaximum_eq_of_mask {ι : Type*} [Fintype ι]
    (χ ψ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (hψ : ∀ i, (ψ i).residue ≠ 1) (T : ℝ)
    (hmask : ∀ i, ∀ I : Ideal O, idealCoeff (χ i) I =
      if IsCoprime I (χ i).modulus then idealCoeff (ψ i) I else 0) :
    zeroMaximum χ hχ T = zeroMaximum ψ hψ T := by
  apply le_antisymm
  · apply zeroMaximum_le_of_zero_inclusion χ ψ hχ hψ T
    intro i
    exact ⟨i, fun s hs hz => (positive_zeros_eq_of_mask (χ i) (ψ i)
      (hχ i) (hmask i) hs).mp hz⟩
  · apply zeroMaximum_le_of_zero_inclusion ψ χ hψ hχ T
    intro i
    exact ⟨i, fun s hs hz => (positive_zeros_eq_of_mask (χ i) (ψ i)
      (hχ i) (hmask i) hs).mpr hz⟩

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.FiniteDeletionBins -/
