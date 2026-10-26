/- Genuine root selected LOW and marked HIGH to the literal initial live budget.
Copyright (c)2026 Zhongpai Gao. Native analytic components by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootPaidBudget
import Candidate.Research.RecursiveAffine.RootBudgetUniform
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootGiven
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePhysicalSelection

noncomputable local instance rootLiteralPaidLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
local instance rootLiteralBinding : Cycle153.MarkedRootPrice.RootLedgerBinding rootLiteralPaidLedger :=
  Cycle153.MarkedRootPrice.fixedRootLedgerBinding
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace OAI.SevenEighths.Cycle153RootInitialAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource Cycle63Moment
open CenteredMomentSecondHeightFamily Cycle63InitialMass Cycle153RegionalLow CenteredMomentAllocatedRayDictionary
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance rootLiteralFinite : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

private theorem root_source_gates_actual_card {ι : Type*} [Fintype ι]
    (s : Input ι)(p : Profiles (1/4) (9/4))(N : ℕ)(Cs Z : ℝ)
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z) :
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z where
  card := le_rfl
  controls := caps.controls
  lower := caps.lower
  lo := caps.lo
  hi := caps.hi
  endpoints := caps.endpoints
  scales := caps.scales
  profile₁ := caps.profile₁
  profile₂ := caps.profile₂
  zero₁ := caps.zero₁
  zero₂ := caps.zero₂
  support₁ := caps.support₁
  support₂ := caps.support₂
  volume := caps.volume
  volumeLog := caps.volumeLog
  sourcePositive := caps.sourcePositive
  sourceCap := caps.sourceCap
  poolCap := caps.poolCap
  plain₁ := caps.plain₁
  plain₂ := caps.plain₂
  plain₃ := caps.plain₃
  plain₄ := caps.plain₄

/-- The sole recursive source obligation, at the literal initial affine input.
Its conclusion is exactly native RegionalLowSelectedAt, with the actual
root return and the same original weights, masks and profiles. -/
def RecursiveRootLowAt
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (eta eta0 : Character) (Q : Ideal O)
    (hQM : Q≤M) (hQ72 : internalQ Q eta0≤Ideal.span {(72:O)})
    (bPhi mesh tau Cs : ℝ) (Sp : Finset (ℕ×ℕ)) (degree : ℕ) (K Z : ℝ)
    (hmesh0 : 0≤ mesh) : Prop :=
  ∀(hZ : 1<Z) (hT : 2<Z^g.τ) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50)) (t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤ mesh) → 0≤height → (∀i,|freq i|≤height) →
    1+|t|+height≤Z^tau →
  ∀(Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Set.Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (p : Profiles (1/4) (9/4)) (X1 X2 : ℝ)
    (hX1 : 0<X1) (hX2 : 0<X2),
    Cycle63.AffineLedger.PlainWindow (length Z X1) (length Z X2) (∑i,w i) →
  let state:=fixedParentState eta (internalQ Q eta0) Phi bPhi Z 1 hZ (by norm_num) hsPhi hpPhi;
  let inp:=affineInput M H hH eta0 θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num)
    (Cycle63.AffineLedger.comparisonLength (length Z X1) (length Z X2) (∑i,w i)) t X1 X2 hX1 hX2;
  ∀caps : GeometryAffineLowSourceGates inp p Cs Z,
  ∀hmatch : Matches M H hH inp eta0 θ w σ freq W 2 Z,
  ∀(hfit : 1+Real.logb Z (inp.η.modulus.absNorm:ℝ)≤1+g.μ/16)
    (hw : ∀i,0≤w i) (hwL : ∀i,w i≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hwr : ∀i,w i/31≤1) (hwm : ∀i,w i≤ mesh)
    (hheight : 0≤height) (hfreq : ∀i,|freq i|≤height)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑i,Real.logb Z (inp.P i) ∧
      (∑i,Real.logb Z (inp.P i))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z inp.X₁+length Z inp.X₂+Cycle63.AffineLedger.lam*(∑i,Real.logb Z (inp.P i))≤Cycle63.AffineLedger.B),
  RegionalLowSelectedAt M H hH W hβlo g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs
    (fun _ _ _=>True) (fun _ _ _ _ _=>True) Sp degree K eta0 Q hQM hQ72 Z
    (Z^(Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i,w i)))-3*g.δ)) hZ inp p caps θ w σ freq hmatch
    1 1 0 1 one_ne_zero squarefree_one (by norm_num)
    (by simp)
    (by norm_num) le_rfl hfit trivial height mesh hw hwL hwr hmesh0 hwm hσ hheight hfreq hT hβhi hzslot haff

/-- Actual native root source assembly. All profile controls, constants and
finite-subset unions precede Z and the moving source. The HIGH input is the
checked literal marked spec; the only recursive premise is the actual LOW
producer above. No moment or returned-count bound is an input. -/
theorem literal_root_budget_from_recursive_low
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (epsAffine mesh epsMass tau : ℝ)
    (heps : 0<epsAffine) (hepsMass : 0≤epsMass) (hmesh0 : 0≤ mesh)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (hμ : g.μ=geometryLossUnit 1 epsAffine)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130 (3*((Fintype.card α:ℝ)+2)) (Fintype.card α))
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hmarkedMesh : mesh≤Cycle63MarkedPlain.markedRawMesh*Cycle63MarkedPlain.markedCoreMin)
    (hreserve : 128*g.μ≤Cycle63.AffineLedger.lowReserve)
    (eta eta0 : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ : internalQ Q eta0≠0) (hQt : internalQ Q eta0≠⊤)
    (hQ72 : internalQ Q eta0≤Ideal.span {(72:O)}) (bPhi : ℝ)
    (hLow : ∀Cs : ℝ,1≤Cs → ∀Psi : 𝓢(ℝ,ℂ),
      Function.support (Psi:ℝ→ℂ)⊆Set.Icc (-1) (bPhi+1) → (∀x,0≤(Psi x).re) →
      ∀T : Finset α,∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,∃K : ℝ,0≤K ∧
        ∀ᶠ Z : ℝ in atTop,RecursiveRootLowAt (α:=T) M H hH W hW.continuous hWs hβlo hβhi g
          eta eta0 Q hQM hQ72 bPhi mesh tau Cs Sp degree K Z hmesh0)
    (hHigh : ∀T : Finset α,∃P : HighSourceParameters,P.e=g.e ∧ P.τ=g.τ ∧
      ∃SH : Finset (ℕ×ℕ),∃dh : ℕ,∃KH : ℝ,0≤KH ∧ ∀ᶠ Z : ℝ in atTop,
        Cycle153RootHigh.GeometryAffineMainHighSpec (α:=T) M H hH W hW.continuous hWs hβlo P
          g.μ g.δ (Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ) eta SH dh KH eta0 Q hQM hQ72 Z) :
    LiteralAffineGeometryBudget (α:=α) M H hH W hW.continuous hWs eta eta0 Q bPhi mesh epsMass tau
      (geometryLossUnit 1 epsAffine/64) := by
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW.continuous hWs
  apply literal_affine_geometry_budget_of_subset_budgets M H hH W hW.continuous hWs eta eta0 Q bPhi mesh epsMass tau
    (geometryLossUnit 1 epsAffine/64)
  intro Psi hPsi hpPsi T
  obtain ⟨Sp,degree,K,hK,hLow⟩:=hLow Cs hCs Psi hPsi hpPsi T
  obtain ⟨P,hPe,hPτ,SH,dh,KH,hKH,hHigh⟩:=hHigh T
  obtain ⟨S,D,Croot,hSH,hdh,hCroot,hbudget⟩:=actual_root_parent_budget_from_sources
    M H hH T Sbad hbad W hW hWs hβlo hβhi g epsAffine mesh 0 heps hmesh hmesh0 hμ hδ
    (by norm_num) (by norm_num) (by simpa using hmeshcap) Psi eta0 Q hQM hQ hQt hQ72
    Cs hCs Sp degree K hK SH dh KH hKH hreserve
  refine ⟨D,D,S,Croot,hCroot,?_⟩
  filter_upwards [hbudget,hcaps,hLow,hHigh,
    eventual_affine_polynomial_caps (α:=α) M H hH W hW.continuous
      1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs (by norm_num) (by norm_num) (by norm_num),
    fixed_anchor_width_uniform (fun _ : Fin 1=>eta) 1 (g.μ/16) (by norm_num) (div_pos g.μ_pos (by norm_num)),
    (tendsto_rpow_atTop g.τ_pos).eventually (eventually_gt_atTop (2:ℝ))]
    with Z hb hc hl hh hpoly hanchor htwo
  intro hZ θ w σ freq t height hw hwm hσlo hσhi hheight hfreq hcut Phi hsPhi hpPhi
    p X1 X2 hX1 hX2 hwin state inp key hkey reflected t' u
  let hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50):=fun i=>⟨hσlo i,hσhi i⟩
  have hexc:=hc.2 T eta0 θ w σ freq hσ bPhi state p t X1 X2 hX1 hX2 hw hwin
  have hexcActual:=root_source_gates_actual_card inp p (Fintype.card α) Cs Z hexc
  obtain ⟨caps,hmatch⟩:=actual_affine_low_source_gates M H hH eta0 θ W hW.continuous hWs
    w σ freq hσ state p t X1 X2 hX1 hX2 Cs hZ hw hwin hexcActual
  have hdata:=affine_state_bundle_data M H hH W hW.continuous hWs eta0 θ w σ freq hσ state p
    (by norm_num) t X1 X2 hX1 hX2 hZ hwin
  have hfit : 1+Real.logb Z (inp.η.modulus.absNorm:ℝ)≤1+g.μ/16 := by
    have ha:=hanchor.2 (0:Fin 1) 1 le_rfl
    change 1+Real.logb Z (eta.modulus.absNorm:ℝ)≤1+g.μ/16
    simpa only [mul_one,add_comm] using add_le_add_left ha 1
  let beta:=Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))
  have hβ : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i,Real.logb Z (inp.P i))):=hdata.2.2.2.2
  have hLowGiven:=hl hZ htwo θ w σ freq hσ t height hw hwm hheight hfreq hcut Phi hsPhi hpPhi p
    X1 X2 hX1 hX2 hwin caps hmatch
  have hHighGiven:=Cycle153RootHigh.actual_root_high_given_all (α:=T) M H hH W hW.continuous hWs hβlo
    g P hPe hPτ eta SH dh KH (Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ) eta0 Q hQM hQ72 Z hh
    hZ θ w σ freq hσ bPhi state rfl p t X1 X2 hX1 hX2 height mesh hw hmesh0 hmeshcap hwm
    (fun i=>(hwm i).trans hmarkedMesh) hheight hfreq htwo hβhi hwin Psi
  have hcolumns : ∀I∈finiteColumns (Fintype.piFinset inp.pools),(I.absNorm:ℝ)≤Z^(3:ℝ) := by
    simpa only [show 2*(1:ℝ)+1=3 by norm_num] using
      (hpoly.2 T eta0 θ w σ freq hσ bPhi state p t X1 X2 hX1 hX2 hw hwin).2.2.2.2
  have hAmp : (1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑i,Real.logb Z (inp.P i))/(1:ℝ))))=
      Cycle63.AffineLedger.amp beta := by
    simp only [one_mul,div_one,←Cycle153.MarkedRootPrice.affine_amp_eq,
      ←Cycle153.MarkedRootPrice.affine_cellUpper_eq,←Cycle153.MarkedRootPrice.affine_originalCell_eq]
    rw [←hβ]
  change GeometryAffineHighGiven M H hH g eta0 Q hQM hQ72 hβlo hβhi Z hZ htwo (1/4) (9/4)
    inp p 1 1 1 ((1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑i,Real.logb Z (inp.P i))/(1:ℝ)))))
    Psi _ _ SH dh height
    (KH*Z^((1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑i,Real.logb Z (inp.P i))/(1:ℝ))))+
      Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ)) at hHighGiven
  rw [hAmp] at hHighGiven
  have hPaid:=hb.2 hZ htwo inp p caps θ w σ freq hmatch hcolumns
    1 1 one_ne_zero (by simp) (by norm_num) le_rfl (by rw [←hμ];exact hfit)
    height hw hwm hσ hheight hfreq hdata.2.2.1 hdata.2.2.2.1 beta hβ
    (fun hfit' hwL hwr=>hLowGiven hfit' hw hwL hwr hwm hheight hfreq hdata.2.2.1 hdata.2.2.2.1)
    hHighGiven
    reflected key (by simpa only [Real.rpow_one] using hkey) (inp.t+2*Real.pi*(u-(if reflected then -t' else t')))
  simp only [sub_self,Real.rpow_zero,mul_one] at hPaid
  apply hPaid.trans
  have hside := (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ.le hepsMass)

end
end OAI.SevenEighths.Cycle153RootInitialAssembly
#print axioms OAI.SevenEighths.Cycle153RootInitialAssembly.literal_root_budget_from_recursive_low
