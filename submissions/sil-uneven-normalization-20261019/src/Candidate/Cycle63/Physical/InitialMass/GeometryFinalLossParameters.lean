import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryHighLossChoice
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalParameters

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryLowLossChoice. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- This rate is chosen after the fixed dictionary and source caps. The
mesh, width padding and old-moment loss can still be fixed before them. -/
def geometryLowDictionaryRate (μ d Bmass Bnorm U : ℝ) (N : ℕ) : ℝ :=
  μ/(2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+16)

theorem geometry_low_dictionary_rate_budget
    (μ d Bmass Bnorm U : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm) (hU : 0≤U) :
    let δ:=geometryLowDictionaryRate μ d Bmass Bnorm U N
    0<δ ∧ δ≤μ/16 ∧
      2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ := by
  intro δ
  have hp : 0<δ := by dsimp [δ,geometryLowDictionaryRate];positivity
  have he : δ*(2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+16)=μ :=
    div_mul_cancel₀ _ (by positivity)
  have hc : 0≤2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U := by positivity
  have hprod:=mul_nonneg hp.le hc
  refine ⟨hp,?_,?_⟩ <;> nlinarith

/-- The literal width-one low exponent, including both projector-shell
losses and eight additional unit-rate payments, fits inside two loss units.
These eight fees leave room for the box count, first selection, supported
label payment, both shell counts and subsequent fixed finite partitions.
Each consumer must still show that its own fees fit this displayed ledger. -/
theorem geometry_low_width_one_loss_budget
    (μ d Bmass Bnorm U omega mesh : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm) (hU : 0≤U)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryLowDictionaryRate μ d Bmass Bnorm U N
    μ/8+μ/128+μ/8+2*δ*d*N+
      (2*Cycle63.Arithmetic.q0/9)*(omega+μ/8)+Cycle63.Arithmetic.q0*mesh+
      μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤2*μ := by
  intro δ
  have hb:=(geometry_low_dictionary_rate_budget μ d Bmass Bnorm U N hμ hd hm hn hU).2.2
  change 2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ at hb
  norm_num only [Cycle63.Arithmetic.q0]
  linarith

/-- Any bound supplied by this ledger retains the strict low-branch
saving. This is scalar payment only, not a column-energy hypothesis. -/
theorem geometry_low_width_one_exponent_saving (εaffine loss : ℝ)
    (hε : 0<εaffine) (hloss : loss≤2*geometryLossUnit 1 εaffine) :
    -(7/30000000:ℝ)+loss≤-(7/60000000:ℝ) := by
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hh:=geometry_paid_loss 1 εaffine 1 (7/30000000) loss
    (by norm_num) le_rfl le_rfl (by linarith)
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_low_dictionary_rate_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_low_width_one_loss_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_low_width_one_exponent_saving
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryCommonLossChoice. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- One post-dictionary rate can pay both projector ledgers. The original
mesh and loss unit have already been chosen before the dictionary. -/
def geometryCommonDictionaryRate (μ d Bmass Bnorm U B L : ℝ) (N : ℕ) : ℝ :=
  min (geometryLowDictionaryRate μ d Bmass Bnorm U N)
    (min (geometryHighShellRate μ B L) (μ/128))

theorem geometry_common_dictionary_rate_budget
    (μ d Bmass Bnorm U B L : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤L) :
    let δ:=geometryCommonDictionaryRate μ d Bmass Bnorm U B L N
    0<δ ∧ δ≤μ/128 ∧
      2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ ∧
      B*δ+3*L*δ+δ+8*δ≤μ := by
  intro δ
  have hlo:=geometry_low_dictionary_rate_budget μ d Bmass Bnorm U N hμ hd hm hn hU
  have hhi:=geometry_high_shell_rate_budget μ B L hμ hB hL
  have hδ : 0<δ := by
    exact lt_min hlo.1 (lt_min hhi.1 (by positivity))
  have hδlo : δ≤geometryLowDictionaryRate μ d Bmass Bnorm U N := min_le_left _ _
  have hδhi : δ≤geometryHighShellRate μ B L :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδcap : δ≤μ/128 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hδ,hδcap,?_,?_⟩
  · have hcoef : 0≤2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+8 := by positivity
    have hh:=mul_le_mul_of_nonneg_left hδlo hcoef
    nlinarith [hlo.2.2]
  · have hcoef : 0≤B+3*L+9 := by positivity
    have hh:=mul_le_mul_of_nonneg_left hδhi hcoef
    nlinarith [hhi.2.2]

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_common_dictionary_rate_budget
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryFinalLossParameters. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The post-dictionary rate also pays the ambient slot count. -/
def geometryFinalDictionaryRate (μ d Bmass Bnorm U B Lproj : ℝ) (N : ℕ) : ℝ :=
  min (geometryCommonDictionaryRate μ d Bmass Bnorm U B Lproj N)
    (μ/(64*(d+1)*((N:ℝ)+1)))

def geometryFinalPlainRate (μ d : ℝ) : ℝ := μ/(64*(d+1))

/-- This rate pays dictionary multiplicity; the coarse source loss is μ/8. -/
def geometryFinalErrorDictionaryRate (μ : ℝ) (N : ℕ) : ℝ := μ/(8*((N:ℝ)+1))

def geometryFinalMassRate (μ δ Bmass : ℝ) : ℝ := min δ (μ/(8*(Bmass+1)))

theorem geometry_final_dictionary_budgets
    (μ d Bmass Bnorm U B Lproj : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj) :
    let δ := geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let εplain := geometryFinalPlainRate μ d
    0<δ ∧ δ≤geometryCommonDictionaryRate μ d Bmass Bnorm U B Lproj N ∧
      δ≤μ/128 ∧ 0<εplain ∧
      2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ ∧
      B*δ+3*Lproj*δ+δ+8*δ≤μ ∧
      2*δ*d*N≤μ/32 ∧ 2*d*εplain≤μ/32 ∧
      μ/16+2*d*εplain+2*d*N*δ≤μ/4 := by
  intro δ εplain
  have common := geometry_common_dictionary_rate_budget μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have small := geometry_dictionary_loss_budgets μ d Bmass N hμ hd hm
  rcases small with ⟨hp,hs,he,hma,hplain,hslot,herror,hmass,hjoined⟩
  have hδc : δ≤geometryCommonDictionaryRate μ d Bmass Bnorm U B Lproj N :=
    min_le_left _ _
  have hδs : δ≤μ/(64*(d+1)*((N:ℝ)+1)) := min_le_right _ _
  have hδ : 0<δ := lt_min common.1 hs
  have hlowcoef : 0≤2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+8 := by positivity
  have hhighcoef : 0≤B+3*Lproj+9 := by positivity
  have hlo := mul_le_mul_of_nonneg_left hδc hlowcoef
  have hhi := mul_le_mul_of_nonneg_left hδc hhighcoef
  have hslot' := mul_le_mul_of_nonneg_left hδs (show 0≤2*d*N by positivity)
  refine ⟨hδ,hδc,hδc.trans common.2.1,hp,?_,?_,?_,hplain,?_⟩
  · nlinarith only [hlo,common.2.2.1]
  · nlinarith only [hhi,common.2.2.2]
  · nlinarith only [hslot',hslot]
  · change μ/16+2*d*(μ/(64*(d+1)))+2*d*N*δ≤μ/4
    nlinarith only [hslot',hjoined]

/-- The common cutoff gives the strict low gate as well as both high gates.
The density degree is fixed before this positive height rate is chosen. -/
theorem geometry_final_simultaneous_height_gates
    (μ d Bmass Bnorm U B Lproj : ℝ) (N J : ℕ)
    (hμ : 0<μ) (hd : 0<d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj) :
    let δ := geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let εplain := geometryFinalPlainRate μ d
    let τ := geometryFinalHeight μ d δ (εplain/8) J
    0<τ ∧ τ≤μ/16 ∧ 2*τ<d*δ ∧ 8*τ≤d*δ ∧
      16*τ≤d*(εplain/8) ∧ 2*τ*((J:ℝ)+1)≤μ/8 := by
  intro δ εplain τ
  have rates := geometry_final_dictionary_budgets μ d Bmass Bnorm U B Lproj N
    hμ hd.le hm hn hU hB hL
  have hp : 0<εplain/8 := div_pos rates.2.2.2.1 (by norm_num)
  have ht := geometry_final_height_gates μ d δ (εplain/8) J hμ hd rates.1 hp
  exact ⟨ht.1,ht.2.1,by linarith [ht.1,ht.2.2.1],ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩

theorem geometry_final_error_dictionary_budget (μ : ℝ) (N : ℕ) (hμ : 0<μ) :
    0<geometryFinalErrorDictionaryRate μ N ∧
      ∀n : ℕ,n≤N → geometryFinalErrorDictionaryRate μ N*n≤μ/8 := by
  have ratepos : 0<geometryFinalErrorDictionaryRate μ N := by
    unfold geometryFinalErrorDictionaryRate
    positivity
  refine ⟨ratepos,?_⟩
  intro n hn
  have small := geometry_dictionary_loss_budgets μ 0 0 N hμ le_rfl le_rfl
  have hbudget := small.2.2.2.2.2.2.1
  have hcast : (n:ℝ)≤N := by exact_mod_cast hn
  have hle := mul_le_mul_of_nonneg_left hcast ratepos.le
  change (N:ℝ)*geometryFinalErrorDictionaryRate μ N≤μ/8 at hbudget
  nlinarith only [hle,hbudget]

theorem geometry_final_mass_dictionary_budget
    (μ δ Bmass : ℝ) (hμ : 0<μ) (hδ : 0<δ) (hm : 0≤Bmass) :
    0<geometryFinalMassRate μ δ Bmass ∧ geometryFinalMassRate μ δ Bmass≤δ ∧
      Bmass*geometryFinalMassRate μ δ Bmass≤μ/8 := by
  have hbase : 0<μ/(8*(Bmass+1)) := by positivity
  have hc := div_mul_cancel₀ μ (by positivity : (8*(Bmass+1))≠0)
  have hle := mul_le_mul_of_nonneg_left
    (min_le_right δ (μ/(8*(Bmass+1)))) hm
  refine ⟨lt_min hδ hbase,min_le_left _ _,?_⟩
  change Bmass*min δ (μ/(8*(Bmass+1)))≤μ/8
  nlinarith only [hc,hbase,hle]

/-- The coarse source expansion uses μ/8, not the count-dependent rate. -/
theorem geometry_final_source_expansion_loss (μ : ℝ) (hμ : 0<μ) :
    0<μ/64 ∧ μ/64≤μ/8 := by constructor <;> linarith

theorem geometry_final_error_rate_below_frequency (μ : ℝ) (N : ℕ)
    (hμ : 0<μ) (hN : 7<N) : geometryFinalErrorDictionaryRate μ N<μ/64 := by
  have hn : (7:ℝ)<N := by exact_mod_cast hN
  unfold geometryFinalErrorDictionaryRate
  apply (div_lt_div_iff₀ (by positivity : 0<8*((N:ℝ)+1)) (by norm_num : (0:ℝ)<64)).mpr
  nlinarith only [hμ,hn]

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_dictionary_budgets
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_simultaneous_height_gates
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_error_dictionary_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_mass_dictionary_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_source_expansion_loss
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_error_rate_below_frequency
end
