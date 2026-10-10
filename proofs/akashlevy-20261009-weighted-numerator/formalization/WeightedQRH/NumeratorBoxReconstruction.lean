import WeightedQRH.NumeratorLabelReconstruction
import WeightedQRH.NumeratorFiniteBins

/-! Exact finite normalized dilation decomposition of the reconstructed numerator. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical ContDiff
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def normalizedBox {κ : Type*} (U xi : ℝ) (n j : ℕ) (rho M : ℝ)
    (t : κ → ℝ) (f : κ → ℂ) : ℂ :=
  ((U^(rho*((j : ℝ)*xi))/M : ℝ) : ℂ) * ∑' e, boxSeriesTerm U xi n j t f e

theorem normalized_box_reconstruction {κ : Type*} (U xi : ℝ) (n : ℕ)
    (rho M : ℝ) (hU : 0 < U) (hM : M ≠ 0)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    (∑' e, f e) = ∑ j ∈ Finset.range (n+1),
      ((M*U^(-rho*((j : ℝ)*xi)) : ℝ) : ℂ) * normalizedBox U xi n j rho M t f := by
  rw [tsum_box_decomposition U xi n t f hf]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedBox
  rw [←mul_assoc,←Complex.ofReal_mul]
  have he : M*U^(-rho*((j : ℝ)*xi))*(U^(rho*((j : ℝ)*xi))/M) = 1 := by
    rw [show M*U^(-rho*((j : ℝ)*xi))*(U^(rho*((j : ℝ)*xi))/M) =
      (M/M)*(U^(-rho*((j : ℝ)*xi))*U^(rho*((j : ℝ)*xi))) by ring,
      div_self hM,one_mul,←Real.rpow_add hU]
    simp
  rw [he,Complex.ofReal_one,one_mul]

/-- Every term outside the exact source cutoff is zero, including before any
coefficient mass bound or choice of a row-dependent dilation box. -/
theorem actual_label_term_zero_of_cutoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ) (W : ℝ→ℂ) (a b Y : ℝ)
    (hY : 0 < Y) (hsupp : Function.support W ⊆ Set.Icc a b)
    (e : LabelPacketIndex S u T) (hcut : b*Y < (labelPacketScale S u T e : ℝ)) :
    labelPacketCoefficient S hS η u T hT weight x z e *
      (labelPacketScale S u T e : ℂ)^(-(1/2:ℂ)) *
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
        (Y/(labelPacketScale S u T e : ℝ)) 0 0 = 0 := by
  have hp := MellinReconstruction.polynomial_zero_of_scale_cutoff
    (rowCharacter S hS.prime u) W a b Y
    (labelPacketScale S u T e : ℝ) hsupp hY
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u T e)) hcut
  rw [hp,mul_zero]


/-- A real packet box inherits the actual polynomial choice moment. The cutoff
condition is used only to identify the finite active scales. -/
theorem normalized_dilation_box_fourth {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho U xi : ℝ) (n j : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ι → ℂ) (M E : ℝ) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hrho : 0 ≤ rho)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (L i * N i e) ≤ U^((n : ℝ)*xi))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (L i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖normalizedBox U xi n j rho M (fun e=>max 1 (L i*N i e))
      (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)‖^4 * ‖Q i‖^2) ≤ E := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  let active (i : ι) (e : α i) := valid i e ∧ dilationBox U xi n (max 1 (L i*N i e)) = j
  have hlo (i : ι) (e : α i) (he : active i e) : U^((j : ℝ)*xi) ≤ max 1 (L i*N i e) := by
    have hh := (dilationBox_spec U xi hU hxi n (max 1 (L i*N i e))
      (le_max_left _ _) (hupper i e he.1)).1
    rwa [he.2] at hh
  have hh := packet_box_fourth base A S N hN L rho U ((j : ℝ)*xi) active Q M E hM hU0 hrho
    hlo hs hm hselection
  have ht (i : ι) (e : α i) :
      boxSeriesTerm U xi n j (fun e=>max 1 (L i*N i e))
        (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) e =
      A i e*(N i e:ℂ)^(-(1/2:ℂ))*(if active i e then S i e else 0) := by
    by_cases hv : valid i e
    · by_cases hb : dilationBox U xi n (max 1 (L i*N i e)) = j
      · simp [boxSeriesTerm,active,hv,hb]
      · simp [boxSeriesTerm,active,hv,hb]
    · simp [boxSeriesTerm,active,hv,hzero i e hv]
  simpa only [normalizedBox,ht] using hh


theorem actual_label_series_norm_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y) :
    Summable (fun e : LabelPacketIndex S u T =>
      ‖labelPacketCoefficient S hS η u T hT weight x z e *
      (labelPacketScale S u T e : ℂ)^(-(1/2:ℂ)) *
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
        (Y/(labelPacketScale S u T e : ℝ)) 0 0‖) :=
  MellinReconstruction.reconstructed_series_norm_summable (rowCharacter S hS.prime u) hrow
    W a b ha hsupp hW Y hY _ _
    (fun e=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u T e))
    (label_packet_central_summable S hS firsteps hfirst η u T hT weight x z hx hz hmargin)

theorem errorLabelNumerator_zero_of_no_labels {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (hempty : ¬Nonempty (∀ i:J,T i.val)) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y = 0 := by
  letI : IsEmpty (∀ i:J,T i.val) := not_nonempty_iff.mp hempty
  simp only [errorLabelNumerator,Finset.univ_eq_empty,Finset.sum_empty]

end WeightedQRH.Numerator
