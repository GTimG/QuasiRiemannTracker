/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B054
import Candidate.Bundles.B055
import Candidate.Bundles.B056
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorLabelPrimeBound; sha256 9822a4b9282a8b937f084cd5a33d299edeadb3c9f8c215f88e9ece567be546ad -/
section
                                                      
                                                        

/-! All physical error labels have the same Y^(-4/25) factor as a main prime
slot. Constants are uniform over subsets of a fixed finite slot family. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem error_label_prime_product_bound (epsilon c d B : ℝ) (K : ℕ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ K → ∀ (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
      (Y : ι → ℝ) (W : ι → ℝ → ℂ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ z : ℂ, z.re = 17 / 50 →
      (∏ i, ∑ P : T i, 2880 *
        ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) * (P.val.val.absNorm : ℂ)^(z-1)‖ *
          errorSize u P.val) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon *
          ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  let eta : ℝ := epsilon / (K+1)
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  obtain ⟨C0,hC0,hslot⟩ := error_coefficient_slot_sum eta c d B heta hc hd hB
  let C1 : ℝ := max 1 (2880*C0)
  have hC1 : 1 ≤ C1 := le_max_left _ _
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C1^K,pow_pos hC1pos _,?_⟩
  intro ι _ _ hcard u T Y W hY hWS hWB z hz
  let Nu : ℝ := (Ideal.span {u.val} : Ideal O).absNorm
  have hNu : 1 ≤ Nu := by
    have hn : (Ideal.span {u.val} : Ideal O).absNorm ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    dsimp only [Nu]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hNupos : 0 < Nu := lt_of_lt_of_le zero_lt_one hNu
  have hEach (i : ι) :
      (∑ P : T i, 2880 * ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) *
        (P.val.val.absNorm : ℂ)^(z-1)‖ * errorSize u P.val) ≤
      C1 * Nu^eta * (Y i)^(-(4 / 25 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (hslot u (T i) (Y i) (hY i) (W i) (hWS i) (hWB i) z hz)
      (show (0 : ℝ) ≤ 2880 by norm_num)
    calc
      _ = 2880 * (∑ P : T i, ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) *
          (P.val.val.absNorm : ℂ)^(z-1)‖ * errorSize u P.val) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro P hP; ring
      _ ≤ 2880 * (C0 * Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := hh
      _ ≤ _ := by
        calc
          _ = (2880*C0) * (Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := by ring
          _ ≤ C1 * (Nu^eta * (Y i)^(-(4 / 25 : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (Real.rpow_nonneg hNupos.le _) (Real.rpow_nonneg ((zero_le_one.trans (hY i))) _))
          _ = _ := by ring
  calc
    _ ≤ ∏ i, (C1 * Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun P _ => mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
          (errorSize_nonneg u P.val))
      · intro i hi
        exact hEach i
    _ = C1^(Fintype.card ι) * Nu^(eta*(Fintype.card ι : ℝ)) *
        ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_pow]
      rw [show (Nu^eta)^(Fintype.card ι) = Nu^(eta*(Fintype.card ι : ℝ)) by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNupos.le]]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (zero_le_one.trans (hY i)) _))
      apply mul_le_mul (pow_le_pow_right₀ hC1 hcard) _ (Real.rpow_nonneg hNupos.le _) (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hNu
      dsimp only [eta]
      have hcardR : (Fintype.card ι : ℝ) ≤ K := by exact_mod_cast hcard
      have hden : (0 : ℝ) < K+1 := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorLabelPrimeBound -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorPhysicalPacketMass; sha256 a8d6890e7418f7dcc0ba3518a61be43b0a36a618063dcf10ad4cdd10dee41f71 -/
section
                                                          
                                                              

/-! Actual error-label coefficient mass, with every physical prime label summed
and with the final subpower loss chosen independently of the label count. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_physical_label_mass (epsilon c d B : ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (W : ι → ℝ → ℂ) (Y : ι → ℝ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon * ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  obtain ⟨C1,hC1,hmass⟩ := actual_label_packet_mass (ι:=ι) (epsilon/2) (by linarith)
  obtain ⟨C2,hC2,hprime⟩ := error_label_prime_product_bound (epsilon/2) c d B (Fintype.card ι)
    (by linarith) hc hd hB
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη W Y hY hWS hWB x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
  obtain ⟨hs,hm⟩ := hmass S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  refine ⟨hs,hm.trans ?_⟩
  have hp := hprime ι le_rfl u T Y W hY hWS hWB z hz
  change (∏ i, ∑ P : T i, 2880*‖weight i P‖*errorSize u P.val) ≤ _ at hp
  have hNu : (0 : ℝ) < (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  calc
    _ ≤ (C1*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2)) *
        (C2*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2) * ∏ i, (Y i)^(-(4 / 25 : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [show (C1*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2)) *
          (C2*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2) * ∏ i, (Y i)^(-(4 / 25 : ℝ))) =
          (C1*C2)*((((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2))*
          (((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2))) * ∏ i, (Y i)^(-(4 / 25 : ℝ)) by ring]
      rw [←Real.rpow_add hNu,show epsilon/2+epsilon/2=epsilon by ring]

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorPhysicalPacketMass -/

/- BEGIN ORIGINAL Cycle25.Numerator.ActualBin; sha256 260397e2359b2235f00cb5fb7bac0e3922fccbb6352e55fe344c12f961a88eaf -/
section
                                                             
                                      

/-! The actual physical numerator on a finite amplitude bin. Its only moment
input is a fourth moment of the original row-character polynomial on active
scales; the coefficient masses and all infinite sums are proved here. -/
noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Classical ContDiff
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

def labelPolynomialPacket {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Yp : ι→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex S u T,
    labelPacketCoefficient S hS η u T hT
      (fun i P=>physicalSlotWeight P.val (W i) (Yp i) z) x z e*
    (labelPacketScale S u T e:ℂ)^(-(1/2:ℂ))*
    HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
      (Y/(labelPacketScale S u T e:ℝ)) 0 0

theorem actual_label_packet_bin_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (kap massEps cp dp Bp : ℝ) (hkap : 7/10 ≤ kap) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < dp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp dp) →
      (∀i y,‖W i y‖≤Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤alpha → alpha≤1 → 0<eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0<a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0<Y →
      ∀(U xi : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L zcap delta loss momentEps Ccount Cmoment : ℝ),
      1≤U → 0≤xi → 1≤Ccount → 1≤Cmoment → 0≤q → q≤delta/2 →
      0≤delta/4 → delta/4≤1 →
      1-alpha-6*eps≤1/2-delta/4 → -(1/100:ℝ)≤1/2-delta/4 →
      1+firsteps≤x.re+(1/2-delta/4) → 0<Ccond →
      (∀i,0≤Cu i) → (∀i,Cu i≤Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*selectedCapacity kap zcap ((j:ℝ)*xi+xi)-loss)≤‖Q j i‖) →
      (∀i,‖P i‖≤U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ))
      (∀j∈Finset.range (n+1),∀e:∀i,LabelPacketIndex S (u i) T,
        (∑i,‖if (labelPacketScale S (u i) T (e i):ℝ)≤b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i):ℝ)))=j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i):ℝ)) 0 0 else 0‖^4 * ‖Q j i‖^2)
          ≤Cmoment*U^(1+momentEps)) →
      (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*zcap/2+(3*R+1+momentEps)/4+loss/2+delta*xi/4) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY U xi n Cu Ccond Q P
    R q L zcap delta loss momentEps Ccount Cmoment hU hxi hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀i,T i→ℂ := fun i P=>physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0
  let M : ℝ := Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ))
  have hU0 : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0<N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0<M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hYp i)) _))
  have hLM (i : κ) : Lc i ≤ 1 := by
    letI : Finite (O ⧸ (Ideal.span {(u i).val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1)
    have hNupos : (0:ℝ)<(Ideal.span {(u i).val}:Ideal O).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1))
    apply (div_le_one (mul_pos hCcond hNupos)).mpr
    exact (hCu i).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast FiniteConductor.absNorm_le_of_le (Ideal.le_radical (I := (Ideal.span {(u i).val}:Ideal O)))) hCcond.le)
  have hms (i : κ) := hmass S hS firsteps hfirst η (u i) T hT hdis hη W Yp hYp hWS hWB x z
    alpha eps (delta/4) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/4))≤M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps≤x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) :=
    actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T) (he : ¬N i e≤b*Y) : Sp i e=0 :=
    MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
      (N i e) hsupp hY (hNp i e) (lt_of_not_ge he)
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e≤b*Y) :
      max 1 (Lc i*N i e)≤U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU hxi (hLM i) (hNp i e).le he hcut
  have hb := packet_weighted_bins (fun i=>labelPacketBase S (u i) T Pbase) A Sp N hNp Lc kap U xi n
    (fun i e=>N i e≤b*Y) Q P R q L zcap delta loss momentEps Ccount Cmoment M hkap hM hU hxi hc hm
    hq hqdelta hcard hzoff hupp hseries (fun i=>(hms i).1) hmassU hselected hfull hselection
  have heq : (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) =
      Y^(-(1/2:ℝ))*(∑i,‖(∑'e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e)*P i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold labelPolynomialPacket
    rw [mul_assoc,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
    rw [show (-(1/2:ℂ)).re=-(1/2:ℝ) by norm_num]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)).trans_eq (by dsimp only [M]; ring)

theorem errorLabelNumerator_eq_packet {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y =
      labelPolynomialPacket S hS η u (fun i:J=>T i.val) (fun i=>hT i.val)
        (fun i=>W i.val) (fun i=>Yp i.val) x z W1 Y := by
  exact errorLabelNumerator_reconstruction S hS firsteps hfirst η u hrow J T hT hdis hη hQ
    W Yp x z hx hz hmargin W1 a b ha hsupp hW Y hY

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.ActualBin -/

/- BEGIN ORIGINAL Cycle25.Numerator.FreeScalarBound; sha256 88235f1bcc0d0e697f35aeda9df81ecb3e3ab54c098e75b6daa4250ccec5cc10 -/
section
                                                           
                                                              
                                                            

/-! The calibrated scalar left after the quotient-free numerator expansion.
It contains no correction packet and consequently incurs no correction norm cost. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification HeckeReciprocalGrowth ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

/-- The detector's actual next-bin bound controls the reciprocal uniformly in
all source exclusions; the remaining principal L-factor lies on Re s = 2.04. -/
theorem numeratorFreeRowScalar_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps) :
    ∃C : ℝ,0 < C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S)
      (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤ C*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0 ≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr,by positivity,?_⟩
  intro S hS hmax η u ι _ ψ B a H i hB ha ha1 hH hbin x z hx hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖ ≤ L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ) < 2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖ ≤ 1 := by
    rw [norm_star]
    exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold numeratorFreeRowScalar
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (1*(L+1))*(Cr*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps) :=
      mul_le_mul (mul_le_mul hcal hl (norm_nonneg _) (by norm_num)) hrec
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exact arithmetic and height costs for the numerator-free scalar. In
particular the row norm exponent is 2 eps rather than the old 3 eps. -/
theorem numeratorFreeRowScalar_arithmetic_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι]
      (ψ : ι→Character) (B a H : ℝ) (i : ℕ),
      2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := numeratorFreeRowScalar_bound e eps he he' heps
  have hF : 0 < (fixedConductorConstant S:ℝ) := by
    exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x z hx hz hxi
  have hh : 0 ≤ H := (abs_nonneg _).trans hxi
  apply (hbound S hS hmax η u ψ B a H i hB ha ha1 hH hbin x z hx hz hxi).trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  apply (mul_le_mul_of_nonneg_left hc hC.le).trans_eq
  ring

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.FreeScalarBound -/
