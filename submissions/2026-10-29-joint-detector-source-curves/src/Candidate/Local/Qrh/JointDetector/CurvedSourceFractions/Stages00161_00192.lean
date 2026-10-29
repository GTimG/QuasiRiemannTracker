/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00161_00192
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99979141844454,99979009239524,99978876606911,99978743946619,99978611258650,99978478543009,99978345799697,99978213028718,99978080230075,99977947403771,99977814549809,99977681668192,99977548758924,99977415822007,99977282857445,99977149865240,99977016845396,99976883797916,99976750722802,99976617620059,99976484489689,99976351331695,99976218146080,99976084932847,99975951692000,99975818423541,99975685127473,99975551803800,99975418452525,99975285073650,99975151667179,99975018233115,99974884771461]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (160+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(72373006928309775570272/89560120430554879479885:Fraction),(24122254142958435587416/29852790143518876493295:Fraction),(24120172573414897546757/29852206810186126493295:Fraction),(382826852965836733852/473835293283386928465:Fraction),(4823202085844192872400/5970208028704125298659:Fraction),(72341788359745122398987/89551370430563629479885:Fraction),(1607456587263234442669/1989991565123675099553:Fraction),(24109768094969968954072/29849290143522376493295:Fraction),(535726393615413125900/663304595781991699851:Fraction),(72316821782273184637183/89544370430570629479885:Fraction),(24103527140553046514911/29847540143524126493295:Fraction),(10329191550303464038706/12791552918653447068555:Fraction),(3442766727517675240984/4263767639551232356185:Fraction),(3442469594988326664857/4263684306217982356185:Fraction),(2065303471508303814622/2558160583730839413711:Fraction),(14455876742090841461594/17906774086116225895977:Fraction),(24091048168370239166998/29844040143527626493295:Fraction),(72266907499512686388842/89530370430584629479885:Fraction),(72260669080934483394328/89528620430586379479885:Fraction),(8028270184214346202162/9947430047843125497765:Fraction),(72248195230553508425909/89525120430589879479885:Fraction),(390497073484033342900/483910110435630429621:Fraction),(4815714863617035828580/5968108028706225298659:Fraction),(14445897421078141760312/17903974086119025895977:Fraction),(2063521492923736663010/2557660583731339413711:Fraction),(729464820108628110718/904205761925238681615:Fraction),(72210783125068146818582/89514620430600379479885:Fraction),(14440909770184841289580/17902574086120425895977:Fraction),(229201001818282524875/284162287081282157079:Fraction),(14438416417238424051200/17901874086121125895977:Fraction),(1950968907991645038982/2419124876502902148105:Fraction),(1603991486596593218540/1989019342902425099553:Fraction)]
abbrev p161 := params 0
abbrev ray161 := rays 0
def bank161 : Fin 1 → Cell := oneBank p161 ray161
theorem signs161 : ∀ j, Signs p161 (bank161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p162 := params 1
abbrev ray162 := rays 1
def bank162 : Fin 1 → Cell := oneBank p162 ray162
theorem signs162 : ∀ j, Signs p162 (bank162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p163 := params 2
abbrev ray163 := rays 2
def bank163 : Fin 1 → Cell := oneBank p163 ray163
theorem signs163 : ∀ j, Signs p163 (bank163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p164 := params 3
abbrev ray164 := rays 3
def bank164 : Fin 1 → Cell := oneBank p164 ray164
theorem signs164 : ∀ j, Signs p164 (bank164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p165 := params 4
abbrev ray165 := rays 4
def bank165 : Fin 1 → Cell := oneBank p165 ray165
theorem signs165 : ∀ j, Signs p165 (bank165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p166 := params 5
abbrev ray166 := rays 5
def bank166 : Fin 1 → Cell := oneBank p166 ray166
theorem signs166 : ∀ j, Signs p166 (bank166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p167 := params 6
abbrev ray167 := rays 6
def bank167 : Fin 1 → Cell := oneBank p167 ray167
theorem signs167 : ∀ j, Signs p167 (bank167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p168 := params 7
abbrev ray168 := rays 7
def bank168 : Fin 1 → Cell := oneBank p168 ray168
theorem signs168 : ∀ j, Signs p168 (bank168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p169 := params 8
abbrev ray169 := rays 8
def bank169 : Fin 1 → Cell := oneBank p169 ray169
theorem signs169 : ∀ j, Signs p169 (bank169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p170 := params 9
abbrev ray170 := rays 9
def bank170 : Fin 1 → Cell := oneBank p170 ray170
theorem signs170 : ∀ j, Signs p170 (bank170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p171 := params 10
abbrev ray171 := rays 10
def bank171 : Fin 1 → Cell := oneBank p171 ray171
theorem signs171 : ∀ j, Signs p171 (bank171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p172 := params 11
abbrev ray172 := rays 11
def bank172 : Fin 1 → Cell := oneBank p172 ray172
theorem signs172 : ∀ j, Signs p172 (bank172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p173 := params 12
abbrev ray173 := rays 12
def bank173 : Fin 1 → Cell := oneBank p173 ray173
theorem signs173 : ∀ j, Signs p173 (bank173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p174 := params 13
abbrev ray174 := rays 13
def bank174 : Fin 1 → Cell := oneBank p174 ray174
theorem signs174 : ∀ j, Signs p174 (bank174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p175 := params 14
abbrev ray175 := rays 14
def bank175 : Fin 1 → Cell := oneBank p175 ray175
theorem signs175 : ∀ j, Signs p175 (bank175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p176 := params 15
abbrev ray176 := rays 15
def bank176 : Fin 1 → Cell := oneBank p176 ray176
theorem signs176 : ∀ j, Signs p176 (bank176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p177 := params 16
abbrev ray177 := rays 16
def bank177 : Fin 1 → Cell := oneBank p177 ray177
theorem signs177 : ∀ j, Signs p177 (bank177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p178 := params 17
abbrev ray178 := rays 17
def bank178 : Fin 1 → Cell := oneBank p178 ray178
theorem signs178 : ∀ j, Signs p178 (bank178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p179 := params 18
abbrev ray179 := rays 18
def bank179 : Fin 1 → Cell := oneBank p179 ray179
theorem signs179 : ∀ j, Signs p179 (bank179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p180 := params 19
abbrev ray180 := rays 19
def bank180 : Fin 1 → Cell := oneBank p180 ray180
theorem signs180 : ∀ j, Signs p180 (bank180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p181 := params 20
abbrev ray181 := rays 20
def bank181 : Fin 1 → Cell := oneBank p181 ray181
theorem signs181 : ∀ j, Signs p181 (bank181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p182 := params 21
abbrev ray182 := rays 21
def bank182 : Fin 1 → Cell := oneBank p182 ray182
theorem signs182 : ∀ j, Signs p182 (bank182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p183 := params 22
abbrev ray183 := rays 22
def bank183 : Fin 1 → Cell := oneBank p183 ray183
theorem signs183 : ∀ j, Signs p183 (bank183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p184 := params 23
abbrev ray184 := rays 23
def bank184 : Fin 1 → Cell := oneBank p184 ray184
theorem signs184 : ∀ j, Signs p184 (bank184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p185 := params 24
abbrev ray185 := rays 24
def bank185 : Fin 1 → Cell := oneBank p185 ray185
theorem signs185 : ∀ j, Signs p185 (bank185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p186 := params 25
abbrev ray186 := rays 25
def bank186 : Fin 1 → Cell := oneBank p186 ray186
theorem signs186 : ∀ j, Signs p186 (bank186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p187 := params 26
abbrev ray187 := rays 26
def bank187 : Fin 1 → Cell := oneBank p187 ray187
theorem signs187 : ∀ j, Signs p187 (bank187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p188 := params 27
abbrev ray188 := rays 27
def bank188 : Fin 1 → Cell := oneBank p188 ray188
theorem signs188 : ∀ j, Signs p188 (bank188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p189 := params 28
abbrev ray189 := rays 28
def bank189 : Fin 1 → Cell := oneBank p189 ray189
theorem signs189 : ∀ j, Signs p189 (bank189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p190 := params 29
abbrev ray190 := rays 29
def bank190 : Fin 1 → Cell := oneBank p190 ray190
theorem signs190 : ∀ j, Signs p190 (bank190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p191 := params 30
abbrev ray191 := rays 30
def bank191 : Fin 1 → Cell := oneBank p191 ray191
theorem signs191 : ∀ j, Signs p191 (bank191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p192 := params 31
abbrev ray192 := rays 31
def bank192 : Fin 1 → Cell := oneBank p192 ray192
theorem signs192 : ∀ j, Signs p192 (bank192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00161_00192
