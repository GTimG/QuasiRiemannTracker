/- Actual child output terminal source receipts survive native base/root transport.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualRootChildPath
import Candidate.Research.RecursiveAffine.TerminalSourceReceipt

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153RegionalLow Cycle153SourceReturn
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=alpha) M H} {j k : Fin 4}

structure ReturnedFamilyTerminalFacts {start count : ℕ} {eta : Character} {Z B T : ℝ} {v : O}
    (F : SuffixFamily (hH:=hH) start count eta Z B T v) (lossCap Kclass : ℝ) : Prop where
  loss : ∀d p,(F.part d p).loss≤lossCap
  source : ∀d p,TerminalSourceCaps (F.part d p).scale (F.part d p).length (F.part d p).amp
    (Real.logb Z ((Ideal.span {F.multiplier d p}).absNorm:ℝ))
  classCap : ∀d p b,(Fintype.card ((F.part d p).record b).Class:ℝ)≤Kclass

namespace ReturnedFamilyTerminalFacts

private theorem logb_rebase {Z power x : ℝ} (hZ : 1<Z) (hp : 0<power) :
    power*Real.logb (Z^power) x=Real.logb Z x := by
  unfold Real.logb
  rw [Real.log_rpow (zero_lt_one.trans hZ)]
  field_simp [ne_of_gt hp,ne_of_gt (Real.log_pos hZ)]

/-- The same actual classes stay in the record; native loss/physical
exponents acquire exactly the true relative unit. -/
def rebasePower {start count : ℕ} {eta : Character} {Z B T power cap K : ℝ} {v : O}
    (hZ : 1<Z) (hp : 0<power) (hp1 : power≤1) (hB : 0≤B) (hcap : 0≤cap)
    {F : SuffixFamily (hH:=hH) start count eta (Z^power) B T v}
    (facts : ReturnedFamilyTerminalFacts F cap K) :
    ReturnedFamilyTerminalFacts (rebaseDepthReturnedFamily hZ hp hp1 hB F) cap K where
  loss:=by
    intro d p
    change power*(F.part d p).loss≤cap
    exact (mul_le_mul_of_nonneg_left (facts.loss d p) hp.le).trans
      (mul_le_of_le_one_left hcap hp1)
  source:=by
    intro d p
    have hf:=(facts.source d p).scale hp.le hp1
    change TerminalSourceCaps (power*(F.part d p).scale) (power*(F.part d p).length)
      (power*(F.part d p).amp) (Real.logb Z ((Ideal.span {F.multiplier d p}).absNorm:ℝ))
    simpa only [logb_rebase hZ hp] using hf
  classCap:=by
    intro d p b
    change (Fintype.card ((F.part d p).record b).Class:ℝ)≤K
    exact facts.classCap d p b

def rootEq {start count : ℕ} {eta : Character} {Z B T cap K : ℝ} {v v' : O}
    (hv : v=v') {F : SuffixFamily (hH:=hH) start count eta Z B T v}
    (facts : ReturnedFamilyTerminalFacts F cap K) :
    ReturnedFamilyTerminalFacts (suffixFamilyRootEq hv F) cap K :=
  ⟨facts.loss,facts.source,facts.classCap⟩

end ReturnedFamilyTerminalFacts

private theorem traced_terminalFacts_transport {N : ReachableNode C k}
    {base base' unit cap K : ℝ} (he : base=base')
    (F : TracedSuffixFamily (hH:=hH) N base unit)
    (facts : ReturnedFamilyTerminalFacts F.family cap K) :
    ReturnedFamilyTerminalFacts (TracedSuffixFamily.transportBase he F).family cap K := by
  cases he
  exact facts

theorem terminalLossCap_mono (hjk : j.val≤k.val) : terminalLossCap k≤terminalLossCap j := by
  have hh : (j.val:ℝ)≤k.val := by exact_mod_cast hjk
  unfold terminalLossCap
  linarith only [hh]

namespace NodeOutput

def terminalFacts {child : ReachableNode C k}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes) :
    ReturnedFamilyTerminalFacts out.family (terminalLossCap k) C.highClassCap :=
  ⟨out.terminalLoss,out.terminalSource,out.classCap⟩

/-- The actual continuing child supplies all three source facts used by
the native selected forest, with no extra children-cap premise. -/
def parentTerminalFacts {child : ReachableNode C k}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (parent : ReachableNode C j) (hunit : child.unit≤parent.unit)
    (v : O) (hv : child.presentation.mult=v) :
    ReturnedFamilyTerminalFacts (out.parentFamilyAtRoot parent hunit v hv)
      (terminalLossCap k) C.highClassCap := by
  have ht:=traced_terminalFacts_transport (parent.localBase_relative child)
    (⟨out.family,out.path⟩ : TracedSuffixFamily (hH:=hH) child child.localBase child.unit) out.terminalFacts
  have hr:=ht.rebasePower parent.localBase_gt_one (div_pos child.unit_pos parent.unit_pos)
    ((div_le_one parent.unit_pos).mpr hunit) C.normCap_nonneg (terminalLossCap_nonneg k)
  exact hr.rootEq hv

/-- The bare-root rebase preserves actual source caps and native classes.
The explicit terminal loss can later increase only by the separately paid
root shell shift. No parent node is fabricated. -/
def globalTerminalFacts {child : ReachableNode C (0:Fin 4)}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (v : O) (hv : child.presentation.mult=v) :
    ReturnedFamilyTerminalFacts (out.globalFamilyAtRoot v hv) (terminalLossCap (0:Fin 4)) C.highClassCap := by
  have ht:=traced_terminalFacts_transport child.localBase_eq
    (⟨out.family,out.path⟩ : TracedSuffixFamily (hH:=hH) child child.localBase child.unit) out.terminalFacts
  have hr:=ht.rebasePower C.globalBase_gt_one child.unit_pos child.unit_le_one C.normCap_nonneg
    (terminalLossCap_nonneg (0:Fin 4))
  exact hr.rootEq hv

end NodeOutput
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.NodeOutput.parentTerminalFacts
#print axioms OAI.SevenEighths.Cycle153Reachable.NodeOutput.globalTerminalFacts
