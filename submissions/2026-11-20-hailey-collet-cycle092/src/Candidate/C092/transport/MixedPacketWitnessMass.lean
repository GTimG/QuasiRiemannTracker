/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Second-moment transport of the COMPLETE row-dependent error tuple series.
Adapted from Cycle25 weighted_fourth_selection, retaining its source credits. -/
import Candidate.C092.transport.SelectedNonfloorPacket
import Candidate.C092.transport.MixedPacketWitnessKernel

set_option autoImplicit false
namespace QRH.Cycle092.MixedPacketWitness
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CenteredMomentReflectionWeightedEnergy
open Cycle25.Numerator

/-- Independent rowwise choices preserve a second moment under the entire
absolute coefficient mass. No single representative coefficient is selected. -/
theorem weighted_second_selection {Row : Type*} [Fintype Row] {Index : Row→Type*}
    (base : ∀ u,Index u) (weight value : ∀ u,Index u→ℂ) (M E : ℝ) (hM : 0 ≤ M)
    (hs : ∀ u,Summable (fun e=>‖weight u e‖))
    (hm : ∀ u,(∑' e,‖weight u e‖) ≤ M)
    (hselection : ∀ e : ∀ u,Index u,(∑ u,‖value u (e u)‖^2) ≤ E) :
    (∀ u,Summable (fun e=>‖weight u e*value u e‖)) ∧
      (∑ u,‖∑' e,weight u e*value u e‖^2) ≤ M^2*E := by
  let (u : Row) : Nonempty (Index u) := ⟨base u⟩
  have hpoint (u : Row) (e : Index u) : ‖value u e‖^2 ≤ E := by
    have h := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j=>‖value j (Function.update base u e j)‖^2)
      (fun _ _=>sq_nonneg _) (Finset.mem_univ u)
    have hh : ‖value u e‖^2 ≤ ∑ j,‖value j (Function.update base u e j)‖^2 := by simpa using h
    exact hh.trans (hselection (Function.update base u e))
  let v : Row→ℝ := fun u=>⨆ e,‖value u e‖^2
  have hb (u : Row) : BddAbove (Set.range (fun e=>‖value u e‖^2)) :=
    ⟨E,by rintro _ ⟨e,rfl⟩;exact hpoint u e⟩
  have hv (u : Row) (e : Index u) : ‖value u e‖^2 ≤ v u := le_ciSup (hb u) e
  have hv0 (u : Row) : 0 ≤ v u := (sq_nonneg _).trans (hv u (base u))
  have hnorm (u : Row) (e : Index u) : ‖value u e‖ ≤ Real.sqrt (v u) :=
    (Real.le_sqrt (norm_nonneg _) (hv0 u)).mpr (hv u e)
  have hw (u : Row) : Summable (fun e=>‖weight u e*value u e‖) := by
    apply ((hs u).mul_right (Real.sqrt (v u))).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro e
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm u e) (norm_nonneg _)
  have hsum (u : Row) : ‖∑' e,weight u e*value u e‖ ≤ M*Real.sqrt (v u) := by
    apply (norm_tsum_le_tsum_norm (hw u)).trans
    have hle (e : Index u) : ‖weight u e*value u e‖ ≤ ‖weight u e‖*Real.sqrt (v u) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hnorm u e) (norm_nonneg _)
    have hh : (∑' e,‖weight u e*value u e‖) ≤
        ∑' e,‖weight u e‖*Real.sqrt (v u) :=
      (hw u).tsum_le_tsum hle ((hs u).mul_right (Real.sqrt (v u)))
    apply hh.trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm u) (Real.sqrt_nonneg _)
  refine ⟨hw,?_⟩
  calc
    _ ≤ ∑ u,(M*Real.sqrt (v u))^2 :=
      Finset.sum_le_sum (fun u _=>pow_le_pow_left₀ (norm_nonneg _) (hsum u) 2)
    _ = M^2*∑ u,v u := by simp only [mul_pow,Real.sq_sqrt (hv0 _),Finset.mul_sum]
    _ ≤ M^2*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun u e=>‖value u e‖^2) E hselection) (sq_nonneg _)

/-- Full error-label mass at its TRUE max-one dilation transports an earlier
pair moment. The actual ordinary witness and selected original marks stay
fixed through the complete countable coefficient sum. -/
theorem packet_second_selection {Row : Type*} [Fintype Row] {Index : Row→Type*}
    (base : ∀ u,Index u) (A S : ∀ u,Index u→ℂ) (N : ∀ u,Index u→ℝ)
    (hN : ∀ u e,0 < N u e) (L : Row→ℝ) (rho : ℝ)
    (ordinary selected : Row→ℂ) (M E : ℝ) (hM : 0 ≤ M)
    (hs : ∀ u,Summable (fun e=>‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho))
    (hm : ∀ u,(∑' e,‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho) ≤ M)
    (hselection : ∀ e : ∀ u,Index u,
      (∑ u,‖(S u (e u)/((max 1 (L u*N u (e u))^rho:ℝ):ℂ))*ordinary u*selected u‖^2) ≤ E) :
    (∑ u,‖(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*S u e)*ordinary u*selected u‖^2) ≤ M^2*E := by
  let D (u : Row) (e : Index u) : ℝ := max 1 (L u*N u e)^rho
  have hD (u : Row) (e : Index u) : 0 < D u e :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  let weight (u : Row) (e : Index u) := A u e*(N u e:ℂ)^(-(1/2:ℂ))*(D u e:ℂ)
  let value (u : Row) (e : Index u) := (S u e/(D u e:ℂ))*ordinary u*selected u
  have hn (u : Row) (e : Index u) : ‖weight u e‖ =
      ‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho := by
    dsimp [weight]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN u e),
      show (-(1/2:ℂ)).re=-(1/2:ℝ) by norm_num,
      Complex.norm_real,Real.norm_of_nonneg (hD u e).le]
  have hw : ∀ u,Summable (fun e=>‖weight u e‖) := by intro u;simpa only [hn] using hs u
  have hwm : ∀ u,(∑' e,‖weight u e‖) ≤ M := by intro u;simpa only [hn] using hm u
  have hh := weighted_second_selection base weight value M E hM hw hwm hselection
  have he (u : Row) (e : Index u) : weight u e*value u e =
      (A u e*(N u e:ℂ)^(-(1/2:ℂ))*S u e)*ordinary u*selected u := by
    dsimp [weight,value]
    have hd : (D u e:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hD u e).ne'
    field_simp
  have hsum (u : Row) : (∑' e,weight u e*value u e) =
      (∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*S u e)*ordinary u*selected u := by
    simp_rw [he]
    rw [tsum_mul_right,tsum_mul_right]
  simpa only [hsum] using hh.2

#print axioms weighted_second_selection
#print axioms packet_second_selection
end
end QRH.Cycle092.MixedPacketWitness
