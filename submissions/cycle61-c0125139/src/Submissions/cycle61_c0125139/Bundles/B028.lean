/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B025
import Submissions.cycle61_c0125139.Bundles.B027
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowChoiceEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowDyads
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFixedMember
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFull
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFullBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowGlobalBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowInactiveEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowMemberBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowMemberGeometry

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Reflection.FullBudget; sha256 2e88c7099fc8ca77f36a603078a1a06c19ff5e529de84202d5940cf898d37dde -/
section
                                    
                                                   
                                                     
                                                           
                                                             

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Reflection/LowFull, Reflection/LowFullBudget, Reflection/LowGlobalBudget.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle61. -/
namespace OAI
noncomputable section
namespace SevenEighths.Cycle61LowReflection
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}
theorem original_low_sector_full_energy
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool) :
    ∃ (degree degreeTail : ℕ) (C Ctail Z₀ : ℝ), 0<C ∧ 0<Ctail ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤Cycle61.Arithmetic.ell → ell0≤Cycle61.Arithmetic.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,Cm,Z₀,hCm,hZ₀,henergy⟩ := original_low_sector_retained_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail
    (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) lo hi hlo Adecay W hWs hW
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤Cshape := by dsimp [Cshape];positivity
  have hCtail : 0<Ctail := by dsimp [Ctail];positivity
  refine ⟨degree,degreeTail,2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hNlevel hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    gcongr
    linarith only
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
      nlinarith only [hp]
end
end
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}
theorem original_low_sector_full_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤Cycle61.Arithmetic.ell → ell0≤Cycle61.Arithmetic.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget s Lcap δ saving hδ
  obtain ⟨degree,degreeTail,Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := original_low_sector_full_energy
    (Nlevel:=Nlevel) Adecay ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨deg,Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have h128 : 128≤Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith only [hp]
end
end
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}
theorem original_low_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤Cycle61.Arithmetic.ell → ell0≤Cycle61.Arithmetic.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  let q := (Fintype.card (Eis⧸Ideal.span {Nlevel^2}):ℝ)
  have hq : 0≤q := Nat.cast_nonneg _
  refine ⟨degree,q^3*C+1,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      exact henergy J I F Q Q₀ hJ hI hQ hpower hmask A
        Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
        hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
        hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
        hFcap hscap hpool (fullRaySector Nlevel rows r₀) (fullRaySector Nlevel Pset p₀) S
        (fun K hK => hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
        (fun K hK => hrowcop K (Finset.mem_filter.mp hK).1)
        (fun P hP => hprod P (Finset.mem_filter.mp hP).1)
        (fun P hP => hScop P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSN P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSchar P (Finset.mem_filter.mp hP).1)
        θ r aw hqk hqp
        (fun K hK => hKr K (Finset.mem_filter.mp hK).1)
        (fun P hP => hPr P (Finset.mem_filter.mp hP).1)
        (fun K hK => hr K (Finset.mem_filter.mp hK).1)
        (fun P hP => haw P (Finset.mem_filter.mp hP).1))
  apply hs.trans
  change q^3*(C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2))≤_
  have hp : 0≤(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith
end
end
end SevenEighths.Cycle61LowReflection
end
end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Reflection.FullBudget -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Reflection.MemberBudget; sha256 1df784c64617b4fba44f679a986924084e3e5902a27b14eb38c61e6353c34b7c -/
section
                                    
                                                 
                                                             
                                                               

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Reflection/LowMemberBudget, Reflection/LowMemberGeometry.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle61. -/
namespace OAI
noncomputable section
namespace SevenEighths.Cycle61LowReflection
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}
theorem original_low_member_tuple_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤Cycle61.Arithmetic.ell → ell0≤Cycle61.Arithmetic.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_global_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows tuples hne hmax hgood hinj
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  obtain ⟨D,hD⟩ := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  convert he using 1
  apply Finset.sum_congr rfl
  intro K hK
  congr 2
  exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw).symm
end
end
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}
theorem original_low_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤Cycle61.Arithmetic.ell → ell0≤Cycle61.Arithmetic.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  have hb (i : γ) := original_low_member_tuple_full_budget (Nlevel:=Nlevel)
    ε hε lo hi hlo W hWs hW (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
    ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  choose degree C Z₀ hC hZ₀ henergy using hb
  let degreeAll := ∑ i,degree i
  let CAll := (∑ i,C i)+1
  let ZAll := (∑ i,|Z₀ i|)+2
  have hn (i : γ) : degree i≤degreeAll := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : γ) : C i≤CAll := by
    have hh : C i≤∑ j,C j := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : γ) : Z₀ i≤ZAll := by
    have hh : |Z₀ i|≤∑ j,|Z₀ j| := Finset.single_le_sum (fun j _ => abs_nonneg (Z₀ j)) (Finset.mem_univ i)
    have hh' := le_abs_self (Z₀ i)
    dsimp only [ZAll]
    linarith
  have hCA : 0<CAll := by
    have hh : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1<ZAll := by
    have hh : 0≤∑ i,|Z₀ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine ⟨degreeAll,CAll,ZAll,hCA,hZA,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := henergy i J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((hz i).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  apply (hD θ r aw hqk hqp hKr hPr hr haw).trans
  have hZpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
  have hheight : 1≤1+‖θ‖ := by linarith [norm_nonneg θ]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
  exact mul_le_mul (hc i) (pow_le_pow_right₀ hheight (hn i)) (by positivity) hCA.le
end
end
end SevenEighths.Cycle61LowReflection
end
end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Reflection.MemberBudget -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Reflection.FixedDyads; sha256 fcebed9b48d494630e829ed793a30654d80fb616413db9a3e5c7c88ae0f3202f -/
section
                                    
                                                   
                                                   
                                                      
                                                            

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Reflection/LowFixedMember, Reflection/LowDyads.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle61. -/
namespace OAI
noncomputable section
namespace SevenEighths.Cycle61LowReflection
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}
theorem low_fixed_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ QK QP : ℝ),
      Z₀≤Z → 0≤d → d≤Cycle61.Arithmetic.ell → 0≤ell0 → ell0≤Cycle61.Arithmetic.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart I) →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) →
      QK/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      1≤QK → QK≤2*Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) → 2≤QP → QP/2≤Z^ell0 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(1+ell0+shift)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+504*η-O₀/2) := by
  have hCycle25ell := (And.intro Cycle61.Arithmetic.sixth_lt_ell Cycle61.Arithmetic.ell_lt_fifth)
  let ε := η/(200*(1+η))
  have hε : 0<ε := (low_reflection_parameters η hη).1
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := original_low_member_geometry_uniform a c₀ mode
    ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac (η/8) (by positivity) η hη
    η (η/2) 57 8 hη (by positivity) (by norm_num) 8 2 (by positivity)
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hlogQ⟩ := constant_log_error (Ideal.absNorm Q:ℝ) η (actual_ideal_norm_pos Q hQ) hη
  obtain ⟨Z₄,hZ₄,hlogC⟩ := constant_log_error (2*Ck) η (by positivity) hη
  obtain ⟨Z₅,hZ₅,hlog16⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max Z₅ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))))))
  have hz1 : Z₁≤Z₀ := le_max_left _ _
  have hz2 : Z₂≤Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : Z₅≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hzcap : max 2 (max Ck (Ideal.absNorm Q:ℝ))≤Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨degree,C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q₀ hJ hI hF hpower hmask A Z d ell0 shift O₀ QK QP
    hZ hd hd1 hell hellcap hshift hOeq hIn hKr hK1 hKcap hP2 hPcap
  have hz : 1<Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hZ2 : 2≤Z := (le_max_left _ _).trans (hzcap.trans hZ)
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  have hQZ : (Ideal.absNorm Q:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  obtain ⟨hIcap,hFcap,hK8,hP8,hX8⟩ := low_actual_scale_caps J I Q Q₀ hJ hI hQ hpower hmask A
    Z Ck d ell0 shift η QK QP hZ2 hCk hCkZ hQZ hd hell hellcap hshift hη1 hIn hKcap hPcap
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hXp : 0<Z^(1+ell0+shift) := Real.rpow_pos_of_pos hzpos _
  have hQK : 0<QK := by linarith
  have hQP : 0<QP := by linarith
  have hsc := hscale i G Z (Z^(1+ell0+shift)) QK QP 8 (hz2.trans hZ) hXp hQK.le hQP.le
    hFcap hK8 hP8 hX8
  norm_num only at hsc
  have hO : 0≤O₀ := hOeq ▸ normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero I)
  have hOp : 0<(Ideal.absNorm (rowPowerfulPart I):ℝ) := actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
  have hOn : Z^O₀=(Ideal.absNorm (rowPowerfulPart I):ℝ) := by
    rw [hOeq]
    exact Real.rpow_logb hzpos (ne_of_gt hz) hOp
  have hO2 : O₀≤2 := by
    have hh := Real.logb_le_logb_of_le hz hOp ((original_powerful_norm_le I hI).trans hIcap)
    rw [←Real.rpow_natCast,Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    norm_num at hh
    exact hOeq.symm ▸ hh
  have hza : Real.logb Z (QP/2)≤ell0+η := by
    have hh := Real.logb_le_logb_of_le hz (by positivity : 0<QP/2) hPcap
    rw [Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    linarith
  have hrowlower : Z^(Real.logb Z QK)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [Real.rpow_logb hzpos (ne_of_gt hz) hQK]
    exact hKr
  have hslot8 : QP/2≤Z^(8:ℝ) := by linarith
  have hbudget : ε*(8+8+2*(η/2+57+η))+η/2≤2*η := (low_reflection_parameters η hη).2
  have hh := he i (σ:=σ) J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ (Real.logb Z QK) (Real.logb Z (QP/2)) (1+ell0+shift) d ell0 shift (2*η)
    Ck 1 2 (Z^(1+ell0+shift)) QK QP 8 8
    (hz1.trans hZ) hCk (by norm_num) (by norm_num) hXp hQK hQP hIn
    (by simpa only [div_one,hOn] using le_refl (Ideal.absNorm (rowPowerfulPart I):ℝ)) hrowlower
    (by simpa only [mul_one] using hlogC Z (hz4.trans hZ))
    (by rw [hOeq];linarith) (hlogQ Z (hz3.trans hZ)) hd hd1 hellcap hO hza hshift rfl rfl rfl
    (by rw [Real.logb_rpow hzpos (ne_of_gt hz)]) (by positivity) (by linarith)
    hK8 hslot8 (hlog16 Z (hz5.trans hZ)) hbudget hX8 hK8 hP8 (by linarith)
    hFcap hsc hFcap
  dsimp only at hh ⊢
  intro rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := hh rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKn hPn hr haw
  apply (hD θ r aw hqk hqp hKn hPn hr haw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
end
end
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}
theorem low_dyadic_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤Cycle61.Arithmetic.ell → 0≤ell0 → ell0≤Cycle61.Arithmetic.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let Hrow := (Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
      let Hslot := Z^ell0
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) →
      (∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) →
      (∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2) →
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z^(1+ell0+shift)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+504*η-O₀/2)) := by
  have hCycle25ell := (And.intro Cycle61.Arithmetic.sixth_lt_ell Cycle61.Arithmetic.ell_lt_fifth)
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_fixed_member_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq
    parents rows hparents hsub hbad
  dsimp only
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let Hrow := (Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
  let Hslot := Z^ell0
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let jF := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  have hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
    fun K hK => original_residual_norm_bounds parents J Q hbad (Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d)) hparents K (hsub hK)
  have htupleNorm : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot := fun p hp =>
    ⟨QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2),(hPnorm p hp).2⟩
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
    (s g) (hc₀ g) jF W (Z^(1+ell0+shift)) (fun θ => C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+504*η-O₀/2))
    (fun θ => by positivity)
  intro i j hi hj
  let Rc := divisorDyadicBin rows Hrow i
  let Tc := activeTupleDyad tuples Hslot j
  let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
  let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
  have hTc : Tc.Nonempty := hj
  have hRi : ∀ K∈Rc,Admissible K := fun K hK => hrows K (divisorDyadicBin_subset rows Hrow i hK)
  have hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→Ideal Eis)) :=
    hinj.mono (activeTupleDyad_subset tuples Hslot j)
  have hKr := divisorDyadicBin_bounds rows Hrow hrowNorm i
  have hPr := activeTupleDyad_bounds tuples Hslot htupleNorm j
  obtain ⟨K,hK⟩ := hi
  obtain ⟨I,hI,heI⟩ := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  have hI0 := (hparents I hIp).1
  have hIn := (hparents I hIp).2
  have hKlower : (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [heI]
    convert (hKr K hK).1 using 1 ; ring
  have hKupper : 2*divisorDyadicScale i.val≤2*Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) := by
    have hres : (Ideal.absNorm (rowResidualPart I Q):ℝ)≤(Ideal.absNorm I:ℝ) := by
      rw [rowResidualPart_norm I Q hI0]
      apply div_le_self (Nat.cast_nonneg _)
      exact one_le_mul_of_one_le_of_one_le
        (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
        (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))
    have hs := hKlower.trans (hres.trans hIn)
    linarith
  have hPupper : (2*divisorDyadicScale j.val)/2≤Z^ell0 := by
    convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1 ; dsimp [Hslot] ; ring
  let S := tuplePrimeFamily Tc hTc hm hg
  have hScop : ∀ P∈Tc.image slotTupleProduct,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
    intro P hP
    exact hpair ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSN : ∀ P∈Tc.image slotTupleProduct,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
    intro P hP
    exact hPN ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSchar : ∀ P∈Tc.image slotTupleProduct,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2 := by
    intro P hP
    exact hPchar ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  obtain ⟨D,hD⟩ := he g J I F Q₀ hJ hI0 hF hpow.symm hmask.symm A
    Z d ell0 shift O₀ (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
    hZ hd hd1 hell hellcap hshift (by rw [hpow];exact hOeq) hIn hKlower
    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper
    Rc Tc hTc hm hg hti hRi hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
  let Dc : CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
      G rows hrows tuples hmax hgood Hrow Hslot i j := fun K p hp =>
    memberTupleControlled Tc hm hg G K.val (hRi K.val K.property) hTc hti (D K) p hp
  refine ⟨Dc,?_⟩
  intro θ r aw hr haw
  have hb := hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert hKr K hK using 1 ; ring_nf)
    (by
      intro P hP
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
      refine ⟨(hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1,?_⟩
      convert hPr p hp using 1 ; ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))
  exact hb
end
end
end SevenEighths.Cycle61LowReflection
end
end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Reflection.FixedDyads -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Reflection.ChoiceEnergy; sha256 c0fe6b532743a0fe4f725686f43a19b4fe06b9c111405b10e57e7d7fa74f9cf0 -/
section
                                    
                                                 
                                                             
                                                               

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Reflection/LowChoiceEnergy, Reflection/LowInactiveEnergy.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle61. -/
namespace OAI
noncomputable section
namespace SevenEighths.Cycle61LowReflection
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}
theorem low_original_choice_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤Cycle61.Arithmetic.ell → 0≤ell0 → ell0≤Cycle61.Arithmetic.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ K : rows,∀ p : supportedSlotChoices lists (poolPrimeFamily J Q Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily lists hmax hgood p.val)).generator Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ p : supportedSlotChoices lists (poolPrimeFamily J Q Q₀).ideal K.val,
        (∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) σ)
          (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+505*η-O₀/2) := by
  have hCycle25ell := (And.intro Cycle61.Arithmetic.sixth_lt_ell Cycle61.Arithmetic.ell_lt_fifth)
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_dyadic_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  obtain ⟨Cb,hCb,hbins⟩ := actual_dyad_count_budget 8 η (by norm_num) hη
  refine ⟨degree,Cb*C,max Z₀ (max 2 Ck),mul_pos hCb hC,hZ₀.trans_le (le_max_left _ _),?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  have hZbase : Z₀≤Z := (le_max_left _ _).trans hZ
  have hCkZ : Ck≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let FF := (poolPrimeFamily J Q Q₀).ideal
  let tuples := fixedSlotTupleSet lists FF
  let hm := originalTupleMax lists FF hmax
  let hg := originalTupleGood lists FF hgood
  have htuples : ∀ p∈tuples,∀ i,p i∈lists i := fun p hp => ((mem_fixedSlotTupleSet lists FF p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Z^ell0 := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  let Hrow := (Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
  let Hslot := Z^ell0
  obtain ⟨Dc,hDc⟩ := he g J F Q₀ hJ hF A Z d ell0 shift O₀
    hZbase hd hd1 hell hellcap hshift hOeq
    parents rows hparents hsub hbad tuples hm hg (fixedSlotTupleSet_product_injective lists FF hdis hprime)
    hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let D := fun (K : rows) (p : supportedSlotChoices lists FF K.val) =>
    memberChoiceControlled lists FF hmax hgood G K.val (hrows K.val K.property)
      (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K) p
  refine ⟨D,?_⟩
  intro θ w hw
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc (s g) (hc₀ g)
        (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(1+ell0+shift)) (fun _ => 1)
        (fixedTupleCoefficient lists w) K p)=
      ∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) := by
    simpa only [dyadicPhysicalTerm,D,one_mul] using member_source_eq_original_choices lists FF hmax hgood G K.val
      (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) 1 w
  have hb := hDc θ (fun _ => 1) (fixedTupleCoefficient lists w) (by simp) (fun p hp => fixedTupleCoefficient_norm lists w hw p)
  have hid : (∑ K : rows,‖∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(1+ell0+shift))
      (fun _ => 1) (fixedTupleCoefficient lists w) K p‖^2)=
      ∑ K : rows,‖∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hsource K)
  apply (hid.symm.trans_le hb).trans
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZbase
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hp : (1:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
  have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J Q) :=
    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) Q)
  have hRpos : 0<Hrow := by dsimp [Hrow];positivity
  have hScap : Hslot≤Z^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Cycle61.Arithmetic.ell_pos,Cycle61.Arithmetic.ell_lt_fifth])
  have hRcap : Hrow≤Z^(8:ℝ) := by
    apply (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hp hm')).trans
    calc
      Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d) ≤ Z*Z^((1-Cycle61.Arithmetic.ell)-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzpos.le _)
      _ = Z^(1+((1-Cycle61.Arithmetic.ell)-2*d)) := by rw [Real.rpow_add hzpos,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Cycle61.Arithmetic.ell_pos,Cycle61.Arithmetic.ell_lt_fifth])
  have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzpos _) hRcap hScap
  calc
    _ ≤ (Cb*Z^(η))*(C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+504*η-O₀/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (Cb*C)*(1+‖θ‖)^degree*Z^(η+(((1-Cycle61.Arithmetic.ell)-d)+504*η-O₀/2)) := by
      rw [Real.rpow_add hzpos];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Cycle61.Arithmetic.ell_pos,Cycle61.Arithmetic.ell_lt_fifth])) (by positivity)
end
end
section

open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}
theorem low_original_inactive_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤Cycle61.Arithmetic.ell → 0≤ell0 → ell0≤Cycle61.Arithmetic.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^((1-Cycle61.Arithmetic.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∀ T : Finset σ,
    ∃ D : ∀ K : rows,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
          Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val)
        (poolPrimeFamily J Q Q₀).ideal K.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
        ∑ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
          (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) T)
          (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2)≤
        (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*
          (C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+505*η-O₀/2)) := by
  have hCycle25ell := (And.intro Cycle61.Arithmetic.sixth_lt_ell Cycle61.Arithmetic.ell_lt_fifth)
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_choice_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar T
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let FF := (poolPrimeFamily J Q Q₀).ideal
  let rowsb := fun b : ∀ i : {i // i∉T},lists i.val => inactiveRowSet rows lists T FF b
  have hbsub (b : ∀ i : {i // i∉T},lists i.val) : rowsb b⊆rows := by
    intro K hK
    exact ((inactiveRows_mem rows lists T FF b K).mp hK).1
  have hbr (b : ∀ i : {i // i∉T},lists i.val) : ∀ K∈rowsb b,Admissible K := fun K hK => hrows K (hbsub b hK)
  have hdisT : Pairwise (fun i j : T => Disjoint (lists i.val) (lists j.val)) := by
    intro i j hij
    exact hdis (fun hv => hij (Subtype.ext hv))
  have hpT : (∏ i : T,H i.val)≤Z^ell0 := by
    rw [Finset.prod_coe_sort]
    apply le_trans _ hprod
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
      (fun i _ => zero_le_one.trans (hH1 i)) (fun i _ _ => hH1 i)
  have hall := fun b : ∀ i : {i // i∉T},lists i.val =>
    he g J F Q₀ hJ hF A Z d ell0 shift O₀
      hZ hd hd1 hell hellcap hshift hOeq
      parents (rowsb b) hparents ((hbsub b).trans hsub) hbad
      (fun i : T => lists i.val) (fun i : T => H i.val) hdisT
      (fun i => hmax i.val) (fun i => hgood i.val) (fun i => hprime i.val) (hbr b)
      (fun i => hH i.val) hpT hGN hGchar (fun K hK => hrowcop K (hbsub b hK))
      (fun i => hLN i.val) (fun i => hLchar i.val)
  choose Db hDb using hall
  let D := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val)
    (p : supportedSlotChoices (fun i : T => lists i.val) FF K.val) =>
      Db b.val ⟨K.val,(inactiveRows_mem rows lists T FF b.val K.val).mpr ⟨K.property,b.property⟩⟩ p
  refine ⟨D,?_⟩
  intro θ w hw
  let f := fun (K : rows) (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val) =>
    ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
      (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) T)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  apply supported_inactive_source_energy rows lists T FF H (fun i P hP => (hprime i P hP).ne_zero)
    hH w hw f (C*(1+‖θ‖)^degree*Z^(((1-Cycle61.Arithmetic.ell)-d)+505*η-O₀/2)) (by positivity)
  intro b
  exact hDb b θ (fun i : T => w i.val) (fun i P => hw i.val P)
end
end
end SevenEighths.Cycle61LowReflection
end
end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Reflection.ChoiceEnergy -/
