/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual attaining descriptor classes are summed on the same original rows.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafAggregate
import Candidate.C092.transport.SourceInverseP6CloseNormTransport
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentEnergyState CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TerminalProfileUniform QRH.Cycle092.SourceInverseP6
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafAttainers_80fb16db93479639_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The actual P6 shifted short source, after exact norm transport, is
precisely the original pair with its complete common mark. -/
theorem terminal_original_product_source {Slot : Type} [Fintype Slot]
    {U Bmask bPhi : ℝ} (s : NaturalState U Bmask bPhi)
    (rows : Finset FreeRow) (hrows : ∀u ∈ rows,s.radial.keep u.val)
    (ηLong : Character) (hmask : s.mask=fixedBadMask*idealGenerator 1)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (hs : Function.support (W₂:ℝ → ℂ)⊆Set.Icc (1/4:ℝ) (9/4))
    (tLong tShort X Y : ℝ) (hY : 0 < Y)
    (physical native : Slot → FreeRow → ℂ)
    (hmark : ∀u ∈ rows,∀j,‖physical j u‖=‖native j u‖) :
    (∑u ∈ rows,‖original ηLong (fixedBadMask*idealGenerator 1) 1 u.val W₁ tLong X*
      original s.character s.mask 1 u.val (twistProfile W₂ 0 tShort) 0 Y*(∏j,native j u)‖^2)=
      StrongPair.finiteEnergyOn Finset.univ rows ηLong s.character W₁ W₂ tLong tShort X Y physical := by
  have h:=terminal_native_plain_energy s rows hrows ηLong s.character rfl hmask W₁ W₂
    (1/4) (9/4) (by norm_num) hs tLong tShort X Y hY (fun _=>0) Finset.univ native
  simp only [nativeEnergy,TerminalActualRow.shortProfile,Bool.false_eq_true,ite_false] at h
  rw [hmask]
  rw [h]
  exact finiteEnergyOn_norm_congr Finset.univ rows ηLong s.character W₁ W₂ tLong tShort X Y native physical
    (fun u hu j _=>(hmark u hu j).symm)

/-- Actual descriptor cover is a sum over the true attaining slots, with
only its genuine finite repetition factor. Native indices may vary by slot. -/
theorem terminal_actual_attainer_aggregate {Slot Idx : Type} [Fintype Slot] [Fintype Idx]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (rows : Finset FreeRow) (old base : Character) (W : ℝ → ℂ)
    (U pay b : ℝ) (θ : Slot → RayQuotient.Characters M H) (w v : Slot → ℝ) (t : ℝ)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ → ℂ) (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ)
    (exponent : ℝ) (hU : 0 < U) (C : Idx → ℝ) (hC : ∀k,0 ≤ C k)
    (cover : ∀u ∈ rows,∃jd,u ∈ descriptorRows M H hH rows old base W U pay b θ w v t jd)
    (bound : ∀jd,(descriptorRows M H hH rows old base W U pay b θ w v t jd).Nonempty  → 
      ∃k,StrongPair.finiteEnergyOn Finset.univ
        (descriptorRows M H hH rows old base W U pay b θ w v t jd)
        η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤ C k*U^exponent) :
    StrongPair.finiteEnergyOn Finset.univ rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤ 
      (Fintype.card Slot:ℝ)*(∑k,C k)*U^exponent := by
  classical
  let classes:=fun jd=>descriptorRows M H hH rows old base W U pay b θ w v t jd
  let E:=fun u : FreeRow=>‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
    ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*∏j,‖mark j u‖^2
  have hE (u : FreeRow):0 ≤ E u := by dsimp [E];positivity
  have hsub (jd : Slot):classes jd⊆rows:=Finset.filter_subset _ _
  have heq (s : Finset FreeRow): StrongPair.finiteEnergyOn Finset.univ s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark=∑u ∈ s,E u :=rfl
  have hsum : (∑u ∈ rows,E u) ≤ ∑jd : Slot,∑u ∈ classes jd,E u := by
    calc
      _  ≤  ∑u ∈ rows,∑jd : Slot,if u ∈ classes jd then E u else 0 := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨jd,hjd⟩:=cover u hu
        have h:=Finset.single_le_sum (s:=Finset.univ) (f:=fun j : Slot=>if u ∈ classes j then E u else 0)
          (fun j _=>by split_ifs;exact hE u;norm_num) (Finset.mem_univ jd)
        rw [if_pos (show u∈classes jd from hjd)] at h
        exact h
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro jd _
        rw [←Finset.sum_filter]
        congr 1
        ext u
        simp only [Finset.mem_filter]
        exact and_iff_right_of_imp (fun hu=>hsub jd hu)
  have hcost (jd : Slot) : (∑u ∈ classes jd,E u) ≤ (∑k,C k)*U^exponent := by
    by_cases hn : (classes jd).Nonempty
    · obtain ⟨k,hk⟩:=bound jd hn
      have hc:=Finset.single_le_sum (fun k _=>hC k) (Finset.mem_univ k)
      exact hk.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty]
      exact mul_nonneg (Finset.sum_nonneg (fun k _=>hC k)) (Real.rpow_nonneg hU.le _)
  rw [heq]
  calc
    _  ≤  ∑jd : Slot,∑u ∈ classes jd,E u := hsum
    _  ≤  ∑_ : Slot,(∑k,C k)*U^exponent := Finset.sum_le_sum (fun jd _=>hcost jd)
    _ = _ := by simp;ring

#print axioms terminal_original_product_source
#print axioms terminal_actual_attainer_aggregate
end
end QRH.Cycle092.RegularColoredForward
