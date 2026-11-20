/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original coefficient packet restricted by its actual max-one dilation. -/
import Candidate.C092.transport.MixedTicketTailsLargePacket
import Candidate.C092.transport.SelectedNonfloorPacket
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open Cycle25.Numerator Cycle25.Weighted Cycle25.Weighted.Numerator
open QRH.Record1252270103Return
namespace QRH.Cycle092.MixedTicketTails
local notation "O" => HeckeFamily.O
variable [Geometry.Parameters]

def largeLabelPolynomialPacket {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Yp : ι→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y Cu Ccond U vcut : ℝ) : ℂ :=
  let weight : ∀i,T i→ℂ := fun i P=>physicalSlotWeight P.val (W i) (Yp i) z
  (Y:ℂ)^(-(1/2:ℂ))*∑'e:LabelPacketIndex S u T,
    labelPacketCoefficient S hS η u T hT weight x z e*(labelPacketScale S u T e:ℂ)^(-(1/2:ℂ))*
    (if U^vcut ≤ max 1 ((Cu/(Ccond*rowNorm u))*(labelPacketScale S u T e:ℝ)) then
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
        (Y/(labelPacketScale S u T e:ℝ)) 0 0 else 0)

theorem label_packet_large_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (massEps cp bProfile Bp : ℝ) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < bProfile) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (Pbase : ∀ i, T i) (W : ι → ℝ → ℂ) (Yp : ι → ℝ),
      (∀ i, 1 ≤ Yp i) → (∀ i, Function.support (W i) ⊆ Set.Icc cp bProfile) →
      (∀ i y, ‖W i y‖ ≤ Bp) → ∀ (x z : ℂ) (alpha eps : ℝ),
      51/100 ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1/1000 →
      x.re = alpha+16*eps → z.re = 17/50 →
      ∀ (κ : Type) [Fintype κ] (u : κ → FreeRow) (W1 : ℝ → ℂ) (a b Y : ℝ),
      0 < a → Function.support W1 ⊆ Set.Icc a b → ContDiff ℝ ∞ W1 → 0 < Y →
      ∀ (cost d U xi ann : ℝ) (n : ℕ) (Cu : κ → ℝ) (Ccond vcut : ℝ)
      (Q : ℕ → κ → ℂ) (P : κ → ℂ) (R q L delta loss momentEps Ccount Cmoment : ℝ),
      0 ≤ cost → 1 < U → 0 ≤ xi → 0 ≤ ann → 1 ≤ Ccount → 1 ≤ Cmoment → 0 ≤ q → q ≤ delta/2 →
      0 ≤ delta/2 → delta/2 ≤ 1 →
      1-alpha-6*eps ≤ 1/2-delta/2 → -(1/100:ℝ) ≤ 1/2-delta/2 →
      1+firsteps ≤ x.re+(1/2-delta/2) → 0 < Ccond →
      (∀ i, 0 ≤ Cu i) →
      (∀ i, Cu i ≤ Ccond*((Ideal.span {(u i).val} : Ideal O).radical.absNorm : ℝ)) →
      (∀ i, ((Ideal.span {(u i).val} : Ideal O).absNorm : ℝ) ≤ U) →
      (∀ i, (rowCharacter S hS.prime (u i)).residue ≠ 1) →
      b*Y ≤ U^((n:ℝ)*xi) → (Fintype.card κ : ℝ) ≤ Ccount*U^R →
      (∀ j ∈ Finset.range (n+1), ∀ i,
        U^(q*QRH.Cycle092.Physical.Selection.scheduledCapacity Geometry.y cost d (2*((j:ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖) →
      (∀ i, ‖P i‖ ≤ U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val} : Ideal O).absNorm : ℝ))
      (∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, LabelPacketIndex S (u i) T,
        (∑ i, ‖if (labelPacketScale S (u i) T (e i) : ℝ) ≤ b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i) : ℝ))) = j
          then (if U^vcut ≤ max 1 ((Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale S (u i) T (e i):ℝ)) then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i) : ℝ)) 0 0 else 0) else 0‖^4*‖Q j i‖^2)
          ≤ Cmoment*U^(1+momentEps)) →
      (∑ i, ‖largeLabelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y (Cu i) Ccond U vcut*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏ i, (Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*QRH.Cycle092.Physical.Selection.zeroCapacity Geometry.y cost d/2+
            (3*R+1+momentEps)/4+loss/2+delta*(2*xi+ann)/4-delta*vcut/4) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι := ι)
    massEps cp bProfile Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY cost d U xi ann n Cu Ccond vcut Q P
    R q L delta loss momentEps Ccount Cmoment hcost hU hxi hann hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    if U^vcut ≤ max 1 ((Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)))*N i e) then
      HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0 else 0
  let M : ℝ := Cmass*U^massEps*∏ i, (Yp i)^(-(4/25:ℝ))
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0 < N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0 < M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le (hYp i)) _))
  have hLM (i : κ) : Lc i ≤ 1 := by
    letI : Finite (O ⧸ (Ideal.span {(u i).val} : Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1)
    have hNupos : (0:ℝ) < (Ideal.span {(u i).val} : Ideal O).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1))
    apply (div_le_one (mul_pos hCcond hNupos)).mpr
    exact (hCu i).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (FiniteConductor.absNorm_le_of_le
        (Ideal.le_radical (I := (Ideal.span {(u i).val} : Ideal O))))) hCcond.le)
  have hms (i : κ) := hmass S hS firsteps hfirst η (u i) T hT hdis hη W Yp hYp hWS hWB x z
    alpha eps (delta/2) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) :
      (∑' e, ‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2)) ≤ M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps ≤ x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e => ‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) := by
    have hh := actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
    change Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*
      HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0‖) at hh
    apply hh.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro e
    dsimp only [Sp]
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero]
      exact norm_nonneg _
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T)
      (he : ¬(N i e ≤ b*Y ∧ U^vcut ≤ max 1 (Lc i*N i e))) : Sp i e=0 := by
    dsimp only [Sp]
    split_ifs with ht
    · exact MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
        (N i e) hsupp hY (hNp i e) (by
          have hn : ¬N i e ≤ b*Y := fun hn=>he ⟨hn,ht⟩
          exact lt_of_not_ge hn)
    · rfl
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e ≤ b*Y ∧ U^vcut ≤ max 1 (Lc i*N i e)) :
      max 1 (Lc i*N i e) ≤ U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU.le hxi (hLM i) (hNp i e).le he.1 hcut
  have hb := packet_large_bins (fun i => labelPacketBase S (u i) T Pbase) A Sp N hNp Lc cost d U xi ann n
    (fun i e => N i e ≤ b*Y ∧ U^vcut ≤ max 1 (Lc i*N i e)) Q P R q L delta loss momentEps Ccount Cmoment M vcut hcost hM hU hxi hann
    hc hm hq hqdelta hcard hzoff hupp (fun _ _ h=>h.2) hseries (fun i => (hms i).1) hmassU hselected hfull (by
      intro j hj e
      convert hselection j hj e using 1
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hn : N i (e i) ≤ b*Y <;>
        by_cases ht : U^vcut ≤ max 1 (Lc i*N i (e i)) <;>
        by_cases hbin : dilationBox U xi n (max 1 (Lc i*N i (e i)))=j <;>
        simp_all only [Sp,Lc,N,if_pos,if_neg,and_self,and_false,false_and,true_and,and_true])
  have heq : (∑ i, ‖largeLabelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y (Cu i) Ccond U vcut*P i‖) =
      Y^(-(1/2:ℝ))*(∑ i, ‖(∑' e, A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e)*P i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold largeLabelPolynomialPacket
    rw [mul_assoc,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
    rw [show (-(1/2:ℂ)).re = -(1/2:ℝ) by norm_num]
    simp only [Sp,A,N,weight,rowNorm,Complex.ofReal_natCast]
    rfl
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)).trans_eq (by dsimp only [M]; ring)

#print axioms label_packet_large_bound
end QRH.Cycle092.MixedTicketTails
