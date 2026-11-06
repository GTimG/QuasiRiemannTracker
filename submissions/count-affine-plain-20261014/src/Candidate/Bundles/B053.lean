/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B048
import Candidate.Bundles.B052

/- BEGIN ORIGINAL Cycle25.Numerator.PacketFourth; sha256 fb7ec41648127fc6482420bfe3ca535930a94101f718545688911657e970370e -/
section
                                                       
                                       
                                           

/-! Fourth-moment removal of row-dependent numerator coefficient packets. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25WeightedNumeratorReflection

theorem packet_fourth_selection {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho : ℝ) (Q : ι → ℂ) (M E : ℝ)
    (hM : 0 ≤ M)
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖S i (e i) / ((max 1 (L i * N i (e i))^rho : ℝ) : ℂ)‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e‖^4 * ‖Q i‖^2) ≤ M^4 * E := by
  let D (i : ι) (e : α i) : ℝ := max 1 (L i * N i e)^rho
  have hD (i : ι) (e : α i) : 0 < D i e :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) rho
  let w (i : ι) (e : α i) := A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * (D i e : ℂ)
  let f (i : ι) (e : α i) := (S i e / (D i e : ℂ)) * (Real.sqrt ‖Q i‖ : ℂ)
  have hnorm (i : ι) (e : α i) : ‖w i e‖ =
      ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L i * N i e)^rho := by
    dsimp only [w]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i e),
      show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num,
      Complex.norm_real,Real.norm_of_nonneg (hD i e).le]
  have hw : ∀ i, Summable (fun e => ‖w i e‖) := by
    intro i
    simpa only [hnorm] using hs i
  have hwm : ∀ i, (∑' e, ‖w i e‖) ≤ M := by
    intro i
    simpa only [hnorm] using hm i
  have hf : ∀ e : ∀ i, α i, (∑ i, ‖f i (e i)‖^4) ≤ E := by
    intro e
    simpa only [f,norm_mul_sqrt_fourth,D] using hselection e
  have hh := weighted_fourth_selection base w f M E hM hw hwm hf
  have he (i : ι) (e : α i) : w i e * f i e =
      (A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e) * (Real.sqrt ‖Q i‖ : ℂ) := by
    dsimp only [w,f]
    have hd : (D i e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hD i e).ne'
    field_simp
  have hsum (i : ι) : (∑' e, w i e * f i e) =
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e) * (Real.sqrt ‖Q i‖ : ℂ) := by
    simp_rw [he]
    exact tsum_mul_right
  simpa only [hsum,norm_mul_sqrt_fourth] using hh.2

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.PacketFourth -/

/- BEGIN ORIGINAL Cycle25.Numerator.DilationBoxes; sha256 f1944cd1037ce284477644095554a7f2de25ead3a4f5716bf57e37a1fed26451 -/
section
                                     
                                        

/-! Finitely many exponent boxes for the actual compactly truncated dilation.
The box count depends on the chosen small width, not on the row scale. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem exponent_boxes_cover (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) :
    ∃ j ∈ Finset.range (n+1), U^((j : ℝ)*xi) ≤ t ∧ t ≤ U^(((j : ℝ)+1)*xi) := by
  induction n with
  | zero =>
    refine ⟨0,by simp,?_,?_⟩
    · simpa using ht
    · have hpow : 1 ≤ U^xi := Real.one_le_rpow hU hxi
      have ht1 : t ≤ 1 := by simpa using hupper
      simpa using ht1.trans hpow
  | succ n ih =>
    by_cases hsmall : t ≤ U^((n : ℝ)*xi)
    · obtain ⟨j,hj,hlo,hhi⟩ := ih hsmall
      refine ⟨j,?_,hlo,hhi⟩
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj) (by omega))
    · refine ⟨n,Finset.mem_range.mpr (by omega),(le_of_lt (lt_of_not_ge hsmall)),?_⟩
      simpa only [Nat.cast_add,Nat.cast_one] using hupper

/-- Compact support bounds every active coefficient dilation by a fixed power of U. -/
theorem active_dilation_upper (U xi L N b Y : ℝ) (n : ℕ)
    (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hL : L ≤ 1) (hN : 0 ≤ N)
    (hcut : N ≤ b*Y) (hY : b*Y ≤ U^((n : ℝ)*xi)) :
    max 1 (L*N) ≤ U^((n : ℝ)*xi) := by
  apply max_le
  · exact Real.one_le_rpow hU (mul_nonneg (Nat.cast_nonneg _) hxi)
  · exact (mul_le_mul_of_nonneg_right hL hN).trans
      (by simpa only [one_mul] using hcut.trans hY)

def dilationBox (U xi : ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  if h : ∃ j ∈ Finset.range (n+1), U^((j : ℝ)*xi) ≤ t ∧ t ≤ U^(((j : ℝ)+1)*xi)
  then Classical.choose h else 0

theorem dilationBox_mem (U xi : ℝ) (n : ℕ) (t : ℝ) :
    dilationBox U xi n t ∈ Finset.range (n+1) := by
  unfold dilationBox
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

theorem dilationBox_spec (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) :
    U^((dilationBox U xi n t : ℝ)*xi) ≤ t ∧
      t ≤ U^(((dilationBox U xi n t : ℝ)+1)*xi) := by
  have he := exponent_boxes_cover U xi hU hxi n t ht hupper
  rw [dilationBox,dif_pos he]
  exact (Classical.choose_spec he).2

theorem dilation_weight_bound (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t rho : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) (hrho : 0 ≤ rho) :
    t^(-rho) ≤ U^(-rho*(dilationBox U xi n t : ℝ)*xi) := by
  have hlo := (dilationBox_spec U xi hU hxi n t ht hupper).1
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (U^((dilationBox U xi n t : ℝ)*xi))^(-rho) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hU0 _) hlo (neg_nonpos.mpr hrho)
    _ = _ := by rw [←Real.rpow_mul hU0.le]; congr 1; ring

theorem finite_box_partition {κ : Type*} (U xi : ℝ) (n : ℕ) (t : κ → ℝ) (f : κ → ℂ)
    (e : κ) :
    (∑ j ∈ Finset.range (n+1), if dilationBox U xi n (t e) = j then f e else 0) = f e := by
  rw [Finset.sum_eq_single (dilationBox U xi n (t e))]
  · simp
  · intro j hj hne
    simp only [ite_eq_right (Ne.symm hne)]
  · intro hn
    exact False.elim (hn (dilationBox_mem U xi n (t e)))

def boxSeriesTerm {κ : Type*} (U xi : ℝ) (n j : ℕ) (t : κ → ℝ) (f : κ → ℂ)
    (e : κ) : ℂ := if dilationBox U xi n (t e) = j then f e else 0

theorem boxSeries_summable_norm {κ : Type*} (U xi : ℝ) (n j : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    Summable (fun e => ‖boxSeriesTerm U xi n j t f e‖) := by
  apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro e
  unfold boxSeriesTerm
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f e)

theorem tsum_box_decomposition {κ : Type*} (U xi : ℝ) (n : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    (∑' e, f e) = ∑ j ∈ Finset.range (n+1), ∑' e, boxSeriesTerm U xi n j t f e := by
  rw [←Summable.tsum_finsetSum (fun j hj => (boxSeries_summable_norm U xi n j t f hf).of_norm)]
  apply tsum_congr
  intro e
  exact (finite_box_partition U xi n t f e).symm

theorem norm_tsum_le_boxes {κ : Type*} (U xi : ℝ) (n : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    ‖∑' e, f e‖ ≤ ∑ j ∈ Finset.range (n+1), ‖∑' e, boxSeriesTerm U xi n j t f e‖ := by
  rw [tsum_box_decomposition U xi n t f hf]
  exact norm_sum_le _ _

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.DilationBoxes -/

/- BEGIN ORIGINAL Cycle25.Numerator.PacketBoxes; sha256 1534bb07bb9de5d470ac5fa18390dce092b0b18b4430401c9ed135c1ac35998b -/
section
                                      

/-! Coefficient removal inside a finite dilation box. The polynomial moment
is applied only to active coefficient choices; the resulting packet is
normalized by its actual absolute coefficient mass. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_box_fourth
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho U v : ℝ)
    (active : ∀ i, α i → Prop) [∀ i e, Decidable (active i e)]
    (Q : ι → ℂ) (M E : ℝ) (hM : 0 < M) (hU : 0 < U) (hrho : 0 ≤ rho)
    (hlower : ∀ i e, active i e → U^v ≤ max 1 (L i * N i e))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖if active i (e i) then S i (e i) else 0‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖((U^(rho*v) / M : ℝ) : ℂ) *
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) *
        (if active i e then S i e else 0))‖^4 * ‖Q i‖^2) ≤ E := by
  let B (i : ι) (e : α i) := if active i e then S i e else 0
  let T (i : ι) (e : α i) := ((U^(rho*v) : ℝ) : ℂ) * B i e
  have hfactor (i : ι) (e : α i) :
      ‖T i e / ((max 1 (L i * N i e)^rho : ℝ) : ℂ)‖ ≤ ‖B i e‖ := by
    by_cases ha : active i e
    · have hD : 0 < max 1 (L i * N i e)^rho :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
      have hpow : U^(rho*v) ≤ max 1 (L i * N i e)^rho := by
        calc
          _ = (U^v)^rho := by rw [←Real.rpow_mul hU.le]; congr 1; ring
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hU.le _) (hlower i e ha) hrho
      dsimp only [T]
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _),
        Complex.norm_real,Real.norm_of_nonneg hD.le]
      exact (div_le_iff₀ hD).mpr (by nlinarith [norm_nonneg (B i e)])
    · simp [T,B,ha]
  have hsel : ∀ e : ∀ i, α i,
      (∑ i, ‖T i (e i) / ((max 1 (L i * N i (e i))^rho : ℝ) : ℂ)‖^4 * ‖Q i‖^2) ≤ E := by
    intro e
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans (hselection e)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hfactor i (e i)) 4) (sq_nonneg _)
  have hp := packet_fourth_selection base A T N hN L rho Q M E hM.le hs hm hsel
  have he (i : ι) :
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * T i e) =
      ((U^(rho*v) : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro e
    dsimp only [T]
    ring
  simp only [he] at hp
  have hnorm (i : ι) :
      ‖((U^(rho*v) / M : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2 =
      (‖((U^(rho*v) : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2) / M^4 := by
    rw [Complex.ofReal_div]
    have hmul (z : ℂ) : (((U^(rho*v) : ℝ) : ℂ) / (M : ℂ)) * z = (((U^(rho*v) : ℝ) : ℂ)*z)/(M : ℂ) := by ring
    rw [hmul,norm_div,Complex.norm_real,Real.norm_of_nonneg hM.le,div_pow]
    ring
  change (∑ i, ‖((U^(rho*v) / M : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2) ≤ E
  simp_rw [hnorm]
  rw [←Finset.sum_div]
  exact (div_le_iff₀ (pow_pos hM 4)).mpr (by simpa only [mul_comm E] using hp)

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.PacketBoxes -/

/- BEGIN ORIGINAL Cycle25.Numerator.FiniteBins; sha256 888c1a8e4741dd1d32befd9fa707e93b4e6e627c68729f498f885015c497d054 -/
section
                                    

/-! Finite dilation boxes summed after the weighted fourth-moment estimate.
The coefficient mass stays a single linear factor. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem finite_weighted_dilation_bins {ι : Type*} (s : Finset ι) (n : ℕ)
    (S Q : ℕ → ι → ℂ) (P f : ι → ℂ)
    (kap U R q L z xi delta loss epsilon Ccount Cmoment M : ℝ)
    (hkap : 7/10 ≤ kap)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hxi : 0 ≤ xi)
    (hcard : (s.card : ℝ) ≤ Ccount*U^R)
    (hsplit : ∀ i ∈ s, f i = ∑ j ∈ Finset.range (n+1),
      ((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i ∈ s,
      U^(q*selectedCapacity kap z ((j : ℝ)*xi+xi)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : ∀ j ∈ Finset.range (n+1),
      (∑ i ∈ s, ‖S j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i ∈ s, ‖f i * P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hdelta : 0 ≤ delta := by linarith
  let E : ℝ := q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4
  have hj (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i ∈ s, ‖(((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i) * P i‖) ≤
      M*Ccount*Cmoment*U^E := by
    have hd := weighted_dilation_bin s (S j) (Q j) P kap U R q L z ((j : ℝ)*xi) xi delta
      loss epsilon Ccount Cmoment hkap hU hc hm hq hqdelta (mul_nonneg (Nat.cast_nonneg _) hxi)
      hxi hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(E-11*delta*((j : ℝ)*xi+xi)/84) ≤ U^E :=
      Real.rpow_le_rpow_of_exponent_le hU (by
        have hv : 0 ≤ (j : ℝ)*xi+xi := by positivity
        have := mul_nonneg hdelta hv
        dsimp only [E]
        nlinarith)
    calc
      _ = M * (U^(-delta*((j : ℝ)*xi)/4) * (∑ i ∈ s, ‖S j i * P i‖)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_assoc,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hM (Real.rpow_nonneg hU0.le _))]
        ring
      _ ≤ M * (Ccount*Cmoment*U^(E-11*delta*((j : ℝ)*xi+xi)/84)) :=
        mul_le_mul_of_nonneg_left hd hM
      _ ≤ M * (Ccount*Cmoment*U^E) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by have hc0 := zero_le_one.trans hc; have hm0 := zero_le_one.trans hm; positivity)) hM
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (n+1),
        ‖(((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i) * P i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsplit i hi,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), ∑ i ∈ s,
        ‖(((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i) * P i‖ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (n+1), M*Ccount*Cmoment*U^E := Finset.sum_le_sum hj
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp only [E]; ring

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.FiniteBins -/
