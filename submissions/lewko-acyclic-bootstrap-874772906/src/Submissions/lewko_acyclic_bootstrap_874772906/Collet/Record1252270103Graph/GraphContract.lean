/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite graph consumes actual globally downward initial-energy sources. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.Contract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths

def P (s:Source) : Prop :=
 Record1252270103Source.GlobalSource (s.B:ℝ) (s.L:ℝ) (s.cap:ℝ)
def ParentGood (s:Source) : Prop :=
 0<s.B ∧ s.B≤1 ∧ 1<s.L ∧ 0≤s.cap ∧ s.cap<1
def NFAccounting (s:Source) : Prop :=
 (s.allowance=1/10^12 ∧ s.lowFee=1/10^8 ∧ s.highFee=1/10^7) ∨
 (s.allowance=1/10^17 ∧ s.lowFee=1/10^12 ∧ s.highFee=1/10^10)
lemma nf_accounting_positive {s:Source} (h:NFAccounting s) :
 0<s.allowance ∧ 0<s.lowFee ∧ 0<s.highFee := by
 rcases h with ⟨ha,hl,hh⟩ | ⟨ha,hl,hh⟩ <;> rw [ha,hl,hh] <;> norm_num
def seedK : ℝ := 112445673/25000000
def finalK : ℝ := 11243277/2500000

def SeedStep : Prop := ∀n low:Source,
 (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤seedK →
 SeedSourceValid n low → ParentGood low → P low → P n

def NFStep : Prop := ∀(n low:Source) (high:Option Source),
 (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤finalK →
 SourceValid n low high → ParentGood low → NFAccounting n →
 P low → (∀h∈high,P h) → P n

lemma parent_good_of_source_valid {n low:Source} {high:Option Source}
 (hv:SourceValid n low high) : ParentGood n :=
 ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1⟩
lemma parent_good_of_seed_valid {n low:Source}
 (hv:SeedSourceValid n low) : ParentGood n :=
 ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1⟩
end
end QRH.Record1252270103Graph
