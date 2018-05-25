\begin{code}
module Alpha where

open import GPBindings
open import Atom
open import Swap
open import Fresh
open import Chi
open import FreeVariables
open import List.ListProperties
open import OccurBind

open import Data.Unit hiding (setoid)
open import Data.Sum
open import Relation.Nullary
open import Data.Empty
open import Data.List hiding (unfold;any)
open import Data.List.All
open import Data.Product hiding (swap)
open import Data.List.Any as any hiding (tail;map)
open any.Membership-≡
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)
open import Relation.Binary


-- {- Sorts matters -}
-- ∼data ∼α' (S : Sort){F : Functor} : (G : Functor) → ⟦ G ⟧ (μ F) →  ⟦ G ⟧ (μ F) → Set where
--   ∼αV    : {n : V}{S' : Sort}    → ∼α' S (|v| S') n      n
--   ∼α1    :                         ∼α' S |1|      tt     tt
--   ∼αE    : {B : Set}{b : B}      → ∼α' S (|E| B)  b      b
--   ∼αEf   : {G : Functor}{e e' : ⟦ G ⟧ (μ G)}
--          → ∼α' S G e e'          → ∼α' S (|Ef| G) (⟨ e ⟩) (⟨ e' ⟩)
--   ∼αR    : {e e' : ⟦ F ⟧ (μ F)}     
--          → ∼α' S F e e'          → ∼α' S |R|      (⟨ e ⟩) (⟨ e' ⟩)
--   ∼αinj₁ : {F₁ F₂ : Functor}{e e' : ⟦ F₁ ⟧ (μ F)}
--          → ∼α'  S F₁ e e'        → ∼α' S (F₁ |+| F₂) (inj₁ e) (inj₁ e')
--   ∼αinj₂ : {F₁ F₂ : Functor}{e e' : ⟦ F₂ ⟧ (μ F)}
--          → ∼α'  S F₂ e e'        → ∼α' S (F₁ |+| F₂) (inj₂ e) (inj₂ e')
--   ∼αx    : {F₁ F₂ : Functor}{e₁ e₁'  : ⟦ F₁ ⟧ (μ F)}{e₂ e₂'  : ⟦ F₂ ⟧ (μ F)}
--          → ∼α'  S F₁ e₁ e₁' → ∼α'  S F₂ e₂ e₂'
--                                  → ∼α' S (F₁ |x| F₂) (e₁ , e₂) (e₁' , e₂')
--   ∼αb≡S  : (xs : List V){a b : V}{G : Functor}{e e' : ⟦ G ⟧ (μ F)}
--          → ((c : V) → c ∉ xs → ∼α' S {F} G (swapF' F G S a c e) (swapF' F G S b c e')) 
--                                  → ∼α' S (|B| S G)   (a , e)   (b   , e')  
--   ∼αb≢S  : {S' : Sort}{a : V}{G : Functor}{e e' : ⟦ G ⟧ (μ F)} → S ≢ S'           -- This is the only rule that Sort matters !
--          → ∼α' S G e e'          → ∼α' S (|B| S' G)  (a , e)   (a   , e')  

-- ∼α : (S : Sort){F : Functor} → μ F → μ F → Set
-- ∼α S {F} ⟨ e ⟩ ⟨ e' ⟩ = ∼α' S F e e'
infix 10 _∼α_
\end{code}

Sort independent

%<*alpha>
\begin{code}
data ∼αF {F : Functor} : (G : Functor) 
  → ⟦ G ⟧ (μ F) →  ⟦ G ⟧ (μ F) → Set where
    ∼α1    :                         ∼αF |1|           tt         tt
    ∼αR    :  {e e' : ⟦ F ⟧ (μ F)}     
           →  ∼αF F e e'          →  ∼αF |R|           ⟨ e ⟩      ⟨ e' ⟩
    ∼αE    :  {B : Set}{b : B}    →  ∼αF (|E| B)       b          b
    ∼αEf   :  {G : Functor}{e e' : ⟦ G ⟧ (μ G)}
           →  ∼αF G e e'          →  ∼αF (|Ef| G)      ⟨ e ⟩      ⟨ e' ⟩
    ∼α+₁   :  {F₁ F₂ : Functor}{e e' : ⟦ F₁ ⟧ (μ F)}
           →  ∼αF F₁ e e'         →  ∼αF (F₁ |+|  F₂)  (inj₁ e)   (inj₁ e')
    ∼α+₂   :  {F₁ F₂ : Functor}{e e' : ⟦ F₂ ⟧ (μ F)}
           →  ∼αF F₂ e e'         →  ∼αF (F₁ |+|  F₂)   (inj₂ e)   (inj₂ e')
    ∼αx    :  {F₁ F₂ : Functor}{e₁ e₁'  : ⟦ F₁ ⟧ (μ F)}
              {e₂ e₂'  : ⟦ F₂ ⟧ (μ F)}
           →  ∼αF F₁ e₁ e₁'       → ∼αF F₂ e₂ e₂'
                                  →  ∼αF (F₁ |x|  F₂)  (e₁ , e₂)  (e₁' , e₂')
    ∼αV    :  {x : V}{S : Sort}   →  ∼αF (|v| S)       x          x                                  
    ∼αB    :  (xs : List V){S : Sort}{x y : V}{G : Functor}{e e' : ⟦ G ⟧ (μ F)}
           →  ((z : V) → z ∉ xs   → ∼αF G  (swapF G S x z e) (swapF G S y z e')) 
                                  → ∼αF (|B| S G)  (x , e)    (y   , e')  

_∼α_ : {F : Functor} → μ F → μ F → Set
_∼α_ = ∼αF |R|
\end{code}
%</alpha>

\begin{code}
lemma-∼αEf : {F G : Functor}{e e′ : μ F }  → ∼αF {G} (|Ef| F) e e′ → e ∼α  e′  
lemma-∼αEf {F} {G} {⟨ e ⟩} {⟨ e′ ⟩} (∼αEf e∼e′) = ∼αR e∼e′

lemma-∼αR : {F G : Functor}{e e′ : μ F }  → e ∼α e′ → ∼αF {G} (|Ef| F) e e′
lemma-∼αR {F} {G} {⟨ e ⟩} {⟨ e′ ⟩} (∼αR e∼e′) = (∼αEf e∼e′)

-- terminates as the induction is over functor G, no necessary length induction !!!!!
lemma∼swapEquivF : {F G : Functor}{S : Sort}{e e′ : ⟦ G ⟧ (μ F)}
             → ∼αF G e e′
             → (x y : V)
             → ∼αF G (swapF G S x y e) (swapF G S x y e′)
lemma∼swapEquivF {G = |v| z}         ∼αV               x y = ∼αV
lemma∼swapEquivF {G = |1|}           e∼e'              x y = e∼e'
lemma∼swapEquivF {G = |R|}           (∼αR e∼e')        x y = ∼αR   (lemma∼swapEquivF e∼e' x y)
lemma∼swapEquivF {G = |E| B}         e∼e'              x y = e∼e'
lemma∼swapEquivF {G = |Ef| G}        (∼αEf e∼e')       x y = ∼αEf  (lemma∼swapEquivF e∼e' x y)
lemma∼swapEquivF {G = F₁ |+| G₁}     (∼α+₁ e∼e')       x y = ∼α+₁  (lemma∼swapEquivF e∼e' x y) 
lemma∼swapEquivF {G = F₁ |+| G₁}     (∼α+₂ e∼e')       x y = ∼α+₂  (lemma∼swapEquivF e∼e' x y) 
lemma∼swapEquivF {G = F₁ |x| F₂}     (∼αx e∼e' e∼e'')  x y = ∼αx   (lemma∼swapEquivF e∼e' x y) (lemma∼swapEquivF e∼e'' x y)
lemma∼swapEquivF {F} {|B| S G} {S'}  (∼αB xs .{S} {a} {b}  .{G} {e} {e'} f)        
                                     x y 
  with S ≟S S'
lemma∼swapEquivF {F} {|B| S G} .{S}  (∼αB xs .{S} {a} {b}  .{G} {e} {e'} f)        
                                     x y 
 | yes refl  = ∼αB (x ∷ y ∷ xs) 
                   (λ c c∉x∷y∷xs → subst₂  (∼αF G) 
                                           (trans  (lemmaSwapDistributiveF {F} {G}) 
                                                   (cong  (λ w → swapF G S (（ x ∙ y ）ₐ a) w (swapF G S x y e)) 
                                                          (lemma∙ₐc≢a∧c≢b (d∉ab∷xs→d≢a c∉x∷y∷xs ) (d∉ab∷xs→d≢b c∉x∷y∷xs))))
                                           (trans  (lemmaSwapDistributiveF {F} {G}) 
                                                   (cong  (λ w → swapF G S (（ x ∙ y ）ₐ b) w (swapF G S x y e')) 
                                                          (lemma∙ₐc≢a∧c≢b (d∉ab∷xs→d≢a c∉x∷y∷xs ) (d∉ab∷xs→d≢b c∉x∷y∷xs))))
                                           (lemma∼swapEquivF {F} {G} {S} (f c (d∉ab∷xs→d∉xs c∉x∷y∷xs)) x y))
lemma∼swapEquivF {F} {|B| S G} {S'}  (∼αB xs .{S} {a} {b}  .{G} {e} {e'} f)        
                                     x y 
  | no S≢S'  = ∼αB xs (λ c c∉xs → subst₂  (∼αF G) 
                                          (lemmaSwapDistributiveF≢ {F} {G} S≢S') 
                                          (lemmaSwapDistributiveF≢ {F} {G} S≢S') 
                                          (lemma∼swapEquivF {F} {G} {S'} (f c c∉xs) x y))

lemma∼swapEquiv : {F : Functor}{S : Sort}{e e′ : μ F}
             →  e ∼α  e′
             → (x y : V)
             → (swap {F} S x y e) ∼α (swap {F} S x y e′)
lemma∼swapEquiv (∼αR e∼e') x y = ∼αR (lemma∼swapEquivF  e∼e' x y)

lemma∼+B :  {F G : Functor}{e e′ : ⟦ G ⟧ (μ F)}{S : Sort}{a : V} → ∼αF {F} G e e′ → ∼αF {F} (|B| S G) (a , e) (a , e′)  
lemma∼+B {a = a} e∼e' = ∼αB [] (λ c _ → lemma∼swapEquivF e∼e' a c)  

ρF : {F G : Functor} → Reflexive  (∼αF {F} G)
ρF {G = |v| x}               = ∼αV
ρF {G = |1|}                 = ∼α1
ρF {F} {|R|}       {⟨ e ⟩}   = ∼αR  ρF
ρF {G = |E| x}               = ∼αE
ρF {G = |Ef| G}    {⟨ e ⟩}   = ∼αEf ρF
ρF {G = G |+| G₁}  {inj₁ x}  = ∼α+₁ ρF
ρF {G = G |+| G₁}  {inj₂ y}  = ∼α+₂ ρF
ρF {G = G |x| G₁}            = ∼αx  ρF ρF
ρF {G = |B| S G}   {a , e}   = ∼αB [] (λ c _ → lemma∼swapEquivF ρF a c) 

ρ : {F : Functor} → Reflexive (_∼α_ {F})
ρ = ρF

-- automatically derived
σF : {F G : Functor} → Symmetric  (∼αF {F} G)
σF ∼αV              = ∼αV
σF ∼α1              = ∼α1
σF ∼αE              = ∼αE
σF (∼αEf e∼e')      = ∼αEf  (σF e∼e')
σF (∼αR e∼e')       = ∼αR   (σF e∼e')
σF (∼α+₁ e∼e')      = ∼α+₁  (σF e∼e')
σF (∼α+₂ e∼e')      = ∼α+₂  (σF e∼e')
σF (∼αx e∼e' e∼e'') = ∼αx   (σF e∼e') (σF e∼e'')
σF (∼αB xs f)       = ∼αB xs (λ c c∉xs → σF (f c c∉xs))

σ : {F : Functor} → Symmetric  (_∼α_ {F})
σ = σF

τF : {F G : Functor} → Transitive (∼αF {F} G)
τF ∼αV               ∼αV                  = ∼αV
τF ∼α1               ∼α1                  = ∼α1
τF ∼αE               ∼αE                  = ∼αE
τF (∼αEf e∼e')       (∼αEf e'∼e'')        = ∼αEf  (τF e∼e' e'∼e'')
τF (∼αR e∼e')        (∼αR e'∼e'')         = ∼αR   (τF e∼e' e'∼e'')
τF (∼α+₁ e∼e')       (∼α+₁ e'∼e'')        = ∼α+₁  (τF e∼e' e'∼e'')
τF (∼α+₂ e∼e')       (∼α+₂ e'∼e'')        = ∼α+₂  (τF e∼e' e'∼e'')
τF (∼αx e∼e' e∼e'')  (∼αx e'∼e'' e'∼e''') = ∼αx   (τF e∼e' e'∼e'') (τF e∼e'' e'∼e''')
τF (∼αB xs f)        (∼αB ys g)           = ∼αB   (xs ++ ys) (λ c c∉xsys → τF (f c (c∉xs++ys→c∉xs c∉xsys)) (g c (c∉xs++ys→c∉ys {xs = xs} c∉xsys)) )

τ : {F : Functor} → Transitive (_∼α_ {F})
τ = τF

module ∼F-Reasoning (F G : Functor) where
  ≈-preorder : Preorder _ _ _
  ≈-preorder =  
             record { 
             Carrier = ⟦ G ⟧ (μ F);
             _≈_ = _≡_;
             _∼_ = ∼αF G;
             isPreorder =  record {
             isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid (⟦ G ⟧ (μ F))) ;
             reflexive = λ { {M} {.M} refl → ρF};
             trans = τF } }

  import Relation.Binary.PreorderReasoning as PreR
  open PreR ≈-preorder public

module ∼-Reasoning (F : Functor) where
  ≈-preorder : Preorder _ _ _
  ≈-preorder =  
             record { 
             Carrier = μ F;
             _≈_ = _≡_;
             _∼_ = _∼α_;
             isPreorder =  record {
             isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid (μ F)) ;
             reflexive = λ { {M} {.M} refl → ρ};
             trans = τ } }

  import Relation.Binary.PreorderReasoning as PreR
  open PreR ≈-preorder public

mutual
  lemma∼swapCancelF : {F G : Functor}{S : Sort}{e : ⟦ G ⟧ (μ F)}{x y z : V}
            → freshF S z G e
            → freshF S y G e
            → ∼αF G (swapF G S z y (swapF G S x z e)) (swapF G S x y e)
  lemma∼swapCancelF {F} {G} {S} {e} {x} {y}   {z}  z#e y#e   with x ≟v y
  lemma∼swapCancelF {F} {G} {S} {e} {x} {.x}  {z}  z#e x#e | yes refl
    =  begin 
         swapF G S z x (swapF G S x z e)   
       ≈⟨ sym (lemmaSwapIdemComm {F} {G}) ⟩ 
         e
       ≈⟨ lemmaSwapId {F} {G} ⟩ 
         swapF G S x x e
       ∎
    where open ∼F-Reasoning(F)(G)
  lemma∼swapCancelF {F} {G} {S} {e} {x} {y} {z} z#e y#e  | no x≠y with x ≟v z 
  lemma∼swapCancelF {F} {G} {S} {e} {x} {y} {.x} x#e y#e  | no x≠y | yes refl 
    =  begin 
         swapF G S x y (swapF G S x x e)   
       ≈⟨ cong (swapF G S x y) ( sym (lemmaSwapId {F} {G})) ⟩ 
         swapF G S x y e
       ∎
    where open ∼F-Reasoning(F)(G)
  lemma∼swapCancelF {F} {G} {S} {e} {x} {y} {z} z#e y#e  | no x≠y | no x≠z with y ≟v z 
  lemma∼swapCancelF {F} {G} {S} {e} {x} {y} {.y} y#e _  | no x≠y | no x≠z | yes refl
    =  begin 
         swapF G S y y (swapF G S x y e)   
       ≈⟨ sym (lemmaSwapId {F} {G}) ⟩ 
         swapF G S x y e
       ∎
    where open ∼F-Reasoning(F)(G)
  lemma∼swapCancelF {G = |v| S} {S'}  z#e y#e | no x≠y | no x≠z | no y≠z with S ≟S S'
  lemma∼swapCancelF {F} {|v| S} .{S} {e} {x} {y} {z} (freshV≢ z≢e) (freshV≢ y≢e)  | no x≠y | no x≠z | no y≠z | yes refl 
    = subst (λ X → ∼αF (|v| S) X (（ x ∙ y ）ₐ e)) (sym (lemma∙ₐcancel (sym≢ y≢e) (sym≢ z≢e))) ρF
  lemma∼swapCancelF {F} {|v| S}       (freshV≢ z≢e)     (freshV≢S S≢S)      | no x≠y | no x≠z | no y≠z | yes refl = ⊥-elim (S≢S refl)
  lemma∼swapCancelF {F} {|v| S}       (freshV≢S S≢S)     y#e                | no x≠y | no x≠z | no y≠z | yes refl = ⊥-elim (S≢S refl)
  lemma∼swapCancelF {G = |v| S} {S'}  z#e                y#e                | no x≠y | no x≠z | no y≠z | no S≢S'  = ρF
  lemma∼swapCancelF {G = |1|}         z#e                y#e                | no x≠y | no x≠z | no y≠z            = ∼α1
  lemma∼swapCancelF {G = |R|}         (freshR z#e)       (freshR y#e)       | no x≠y | no x≠z | no y≠z            = ∼αR   (lemma∼swapCancelF z#e y#e)
  lemma∼swapCancelF {G = |E| A}       z#e                y#e                | no x≠y | no x≠z | no y≠z            = ∼αE
  lemma∼swapCancelF {G = |Ef| G}      (freshEf z#e)      (freshEf y#e)      | no x≠y | no x≠z | no y≠z            = ∼αEf  (lemma∼swapCancelF z#e y#e)
  lemma∼swapCancelF {G = G |+| G₁}    (freshinj₁ z#e)    (freshinj₁ y#e)    | no x≠y | no x≠z | no y≠z            = ∼α+₁  (lemma∼swapCancelF z#e y#e)
  lemma∼swapCancelF {G = G |+| G₁}    (freshinj₂ z#e)    (freshinj₂ y#e)    | no x≠y | no x≠z | no y≠z            = ∼α+₂  (lemma∼swapCancelF z#e y#e)
  lemma∼swapCancelF {G = F₁ |x| F₂}   (freshx z#e₁ z#e₂) (freshx y#e₁ y#e₂) | no x≠y | no x≠z | no y≠z            = ∼αx   (lemma∼swapCancelF z#e₁ y#e₁)                                                                                                                        (lemma∼swapCancelF z#e₂ y#e₂)
  lemma∼swapCancelF {G = |B| S G} {S'} {w , e} 
                    {x} {y} {z}                 z#we y#we | no x≠y | no x≠z | no y≠z with S ≟S S'
  lemma∼swapCancelF {G = |B| S G} {.S} {w , e}  freshb≡       y#we         | no x≠y | no x≠z | no y≠z | no S≢S'   =  ⊥-elim (S≢S' refl)
  lemma∼swapCancelF {G = |B| S G} {.S} {w , e}  z#we          freshb≡      | no x≠y | no x≠z | no y≠z | no S≢S'   =  ⊥-elim (S≢S' refl)
  lemma∼swapCancelF {G = |B| S G} {S'} {w , e} 
                    {x} {y} {z}                 (freshb z#e)  (freshb y#e) | no x≠y | no x≠z | no y≠z | no S≢S' 
    = lemma∼+B (lemma∼swapCancelF {G = G} {S'} {e} {x} {y} {z} z#e y#e)
  lemma∼swapCancelF {F} {|B| S G} {.S} {w , e} 
                    {x} {y} {z}                 z#we y#we                  | no x≠y | no x≠z | no y≠z | yes refl with x ≟v w
  lemma∼swapCancelF {F} {|B| S G} {.S} {.x , e} 
                    {x} {y} {z}                 z#xe y#xe                  | no x≠y | no x≠z | no y≠z | yes refl | yes refl with x ≟v x
  ... | no x≠x = ⊥-elim (x≠x refl)
  ... | yes refl  with z ≟v z 
  ...             | no z≠z = ⊥-elim (z≠z refl)
  ...             | yes _  = lemma∼+B (lemma∼swapCancelFƛ z#xe y#xe)
  lemma∼swapCancelF {F} {|B| S G} {.S} {w , e} 
                    {x} {y} {z}                 z#we y#we                  | no x≠y | no x≠z | no y≠z | yes refl | no x≠w with w ≟v z
  lemma∼swapCancelF {F} {|B| S G} {.S} {.y , e} 
                    {x} {y} {.y}                z#ze freshb≡               | no x≠y | no _   | no y≠y | yes refl | no _   | yes refl = ⊥-elim (y≠y refl)
  lemma∼swapCancelF {F} {|B| S G} {.S} {.z , e} 
                    {x} {y} {z}                 z#ze (freshb y#e)          | no x≠y | no x≠z | no y≠z | yes refl | no x≠w | yes refl 
    =  begin 
         （ z ∙ y ）ₐ （ x ∙ z ）ₐ z , swapF G S z y (swapF G S x z e)   
       ≈⟨  cong (λ X → （ z ∙ y ）ₐ X , swapF G S z y (swapF G S x z e)) (lemma∙ₐc≡b x z z refl)  ⟩ 
         （ z ∙ y ）ₐ x , swapF G S z y (swapF G S x z e)   
       ≈⟨  cong (λ X → X , swapF G S z y (swapF G S x z e)) (lemma∙ₐc≢a∧c≢b x≠z x≠y)  ⟩ 
         x , swapF G S z y (swapF G S x z e)   
       ∼⟨ ∼αB  (x ∷ y ∷ fvF {F} {G} e) lemmaAux ⟩ 
         z , swapF G S x y e
       ≈⟨ cong (λ X → X , swapF G S x y e) (sym (lemma∙ₐc≢a∧c≢b (sym≢ x≠z) (sym≢ y≠z)))  ⟩ 
         （ x ∙ y ）ₐ z , swapF G S x y e
       ∎
    where 
    lemmaAux : (u : V)(u∉xyzfve : u ∉ (x ∷ y ∷ fvF {F} {G} e)) → ∼αF G (swapF G S x u (swapF G S z y (swapF G S x z e))) (swapF G S z u (swapF G S x y e))
    lemmaAux u u∉xyfve 
      =  begin
            swapF G S x u (swapF G S z y (swapF G S x z e))
          ≈⟨ cong (λ X → swapF G S x u X) (lemmaSwapDistributiveF {F} {G}) ⟩
            swapF G S x u (swapF G S (（ z ∙ y ）ₐ x) (（ z ∙ y ）ₐ z) (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S x u (swapF G S X (（ z ∙ y ）ₐ z) (swapF G S z y e))) (lemma∙ₐc≢a∧c≢b x≠z x≠y)  ⟩
            swapF G S x u (swapF G S x               (（ z ∙ y ）ₐ z) (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S x u (swapF G S x X (swapF G S z y e))) (lemma∙ₐc≡a z y z refl)  ⟩
            swapF G S x u (swapF G S x               y                (swapF G S z y e))
          ≈⟨ lemmaSwapDistributiveF {F} {G} ⟩
             swapF G S (（ x ∙ u ）ₐ x)  (（ x ∙ u ）ₐ y) (swapF G S x u  (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S X  (（ x ∙ u ）ₐ y) (swapF G S x u  (swapF G S z y e))) (lemma∙ₐc≡a x u x refl)  ⟩
             swapF G S u                (（ x ∙ u ）ₐ y) (swapF G S x u  (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S u X (swapF G S x u  (swapF G S z y e))) (lemma∙ₐc≢a∧c≢b (sym≢ x≠y) (sym≢ (d∉ab∷xs→d≢b u∉xyfve)))  ⟩
             swapF G S u                y               (swapF G S x u  (swapF G S z y e))
          ≈⟨ lemmaSwapDistributiveF {F} {G} ⟩
             swapF G S (（ u ∙ y ）ₐ x) (（ u ∙ y ）ₐ u)  (swapF G S u y (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S X (（ u ∙ y ）ₐ u)  (swapF G S u y (swapF G S z y e))) (lemma∙ₐc≢a∧c≢b (sym≢ (d∉ab∷xs→d≢a u∉xyfve)) x≠y)  ⟩
             swapF G S x                (（ u ∙ y ）ₐ u)  (swapF G S u y (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S x X (swapF G S u y (swapF G S z y e))) (lemma∙ₐc≡a u y u refl)  ⟩
             swapF G S x                y                (swapF G S u y (swapF G S z y e))
          ≈⟨ cong (λ X → swapF G S x y X) (lemmaSwapComm {F} {G}) ⟩
             swapF G S x                y                (swapF G S y u (swapF G S z y e))
          ∼⟨ lemma∼swapEquivF (lemma∼swapCancelF y#e u#e) x y ⟩
             swapF G S x                y                (swapF G S z u e)
          ≈⟨ lemmaSwapDistributiveF {F} {G} ⟩
             swapF G S (（ x ∙ y ）ₐ z) (（ x ∙ y ）ₐ u) (swapF G S x y e)
          ≈⟨ cong (λ X → swapF G S X (（ x ∙ y ）ₐ u) (swapF G S x y e)) (lemma∙ₐc≢a∧c≢b (sym≢ x≠z) (sym≢ y≠z))  ⟩
             swapF G S z               (（ x ∙ y ）ₐ u) (swapF G S x y e)
          ≈⟨ cong (λ X → swapF G S z X (swapF G S x y e)) (lemma∙ₐc≢a∧c≢b (d∉ab∷xs→d≢a u∉xyfve) (d∉ab∷xs→d≢b u∉xyfve))  ⟩
             swapF G S z u (swapF G S x y e)
          ∎
      where
      open ∼F-Reasoning(F)(G)
      u#e : freshF S u G e
      u#e = lemmafvF# {F} {G} {u} {S} {e} (d∉ab∷xs→d∉xs {xs = fvF {F} {G} e} u∉xyfve)
    open ∼F-Reasoning(F)(|B| S G)
  lemma∼swapCancelF {F} {|B| S G} {.S} {w , e} 
                    {x} {y} {z}                 z#we y#we             | no x≠y | no x≠z | no y≠z | yes refl | no x≠w | no w≠z with w ≟v y
  lemma∼swapCancelF {F} {|B| S G} {.S} {.y , e} 
                    {x} {y} {.y}                 freshb≡      y#ye     | no x≠y | no _  | no y≠y | yes refl | no x≠w | no w≠y | yes refl = ⊥-elim (y≠y refl)
  lemma∼swapCancelF {F} {|B| S G} {.S} {.y , e} 
                    {x} {y} {z}                 (freshb z#e) y#ye     | no x≠y | no x≠z | no y≠z | yes refl | no x≠w | no w≠z | yes refl
    =  begin
         （ z ∙ y ）ₐ （ x ∙ z ）ₐ y , swapF G S z y (swapF G S x z e)
       ≈⟨  cong (λ X → （ z ∙ y ）ₐ X , swapF G S z y (swapF G S x z e)) (lemma∙ₐc≢a∧c≢b (sym≢ x≠y) y≠z) ⟩
         （ z ∙ y ）ₐ  y            , swapF G S z y (swapF G S x z e)
       ≈⟨ cong (λ X → X , swapF G S z y (swapF G S x z e)) (lemma∙ₐc≡b z y y refl) ⟩
          z                        , swapF G S z y (swapF G S x z e)
       ∼⟨ ∼αB (x ∷ y ∷ fvF {F} {G} e) lemmaAux ⟩
          x                        , swapF G S x y e       
       ≈⟨ cong (λ X → X , swapF G S x y e) (sym (lemma∙ₐc≡b x y y refl)) ⟩       
         （ x ∙ y ）ₐ y             , swapF G S x y e       
       ∎       
    where
    lemmaAux : (u : V)(u∉xyfve : u ∉ x ∷ y ∷ fvF {F} {G} e) → ∼αF G (swapF G S z u (swapF G S z y (swapF G S x z e))) (swapF G S x u (swapF G S x y e))
    lemmaAux u u∉xyfve 
      =  begin
           swapF G S z u (swapF G S z y (swapF G S x z e))
         ≈⟨ lemmaSwapDistributiveF {F} {G} ⟩
           swapF G S (（ z ∙ u ）ₐ z) (（ z ∙ u ）ₐ y) (swapF G S z u (swapF G S x z e))
         ≈⟨ cong (λ X → swapF G S X (（ z ∙ u ）ₐ y) (swapF G S z u (swapF G S x z e))) (lemma∙ₐc≡a z u z refl) ⟩
           swapF G S u               (（ z ∙ u ）ₐ y) (swapF G S z u (swapF G S x z e))
         ≈⟨ cong (λ X → swapF G S u X (swapF G S z u (swapF G S x z e))) (lemma∙ₐc≢a∧c≢b y≠z (sym≢ (d∉ab∷xs→d≢b u∉xyfve))) ⟩
           swapF G S u               y                (swapF G S z u (swapF G S x z e))
         ∼⟨ lemma∼swapEquivF (lemma∼swapCancelF z#e u#e) u y ⟩
           swapF G S u               y                (swapF G S x u e)
         ≈⟨ cong (λ X → swapF G S u X (swapF G S x u e)) (sym (lemma∙ₐc≢a∧c≢b (sym≢ x≠y) (sym≢ (d∉ab∷xs→d≢b u∉xyfve))))  ⟩
           swapF G S u               (（ x ∙ u ）ₐ y) (swapF G S x u e) 
         ≈⟨ cong (λ X → swapF G S X (（ x ∙ u ）ₐ y) (swapF G S x u e)) (sym (lemma∙ₐc≡a x u x refl))  ⟩
           swapF G S (（ x ∙ u ）ₐ x) (（ x ∙ u ）ₐ y) (swapF G S x u e) 
         ≈⟨ sym (lemmaSwapDistributiveF {F} {G}) ⟩
           swapF G S x u (swapF G S x y e)
         ∎
      where
      open ∼F-Reasoning(F)(G)
      u#e : freshF S u G e
      u#e = lemmafvF# {F} {G} {u} {S} {e} (d∉ab∷xs→d∉xs {xs = fvF {F} {G} e} u∉xyfve)
    open ∼F-Reasoning(F)(|B| S G)
  lemma∼swapCancelF {F} {|B| S G} {.S} {.z , e} 
                    {x} {y} {z}                 freshb≡      y#we             | no x≠y | no x≠z | no y≠z | yes refl | no _ | no z≠z | no w≠y = ⊥-elim (z≠z refl)
  lemma∼swapCancelF {F} {|B| S G} {.S} {.y , e} 
                    {x} {y} {z}                 z#we         freshb≡          | no x≠y | no x≠z | no y≠z | yes refl | no _ | no _   | no y≠y = ⊥-elim (y≠y refl)
  lemma∼swapCancelF {F} {|B| S G} {.S} {w , e} 
                    {x} {y} {z}                 (freshb z#e) (freshb y#e)     | no x≠y | no x≠z | no y≠z | yes refl | no x≠w | no w≠z | no w≠y
   =  begin
        （ z ∙ y ）ₐ （ x ∙ z ）ₐ w , swapF G S z y (swapF G S x z e)
      ≈⟨  cong (λ X → （ z ∙ y ）ₐ X , swapF G S z y (swapF G S x z e)) (lemma∙ₐc≢a∧c≢b (sym≢ x≠w) w≠z) ⟩
        （ z ∙ y ）ₐ  w            , swapF G S z y (swapF G S x z e)
      ≈⟨ cong (λ X → X , swapF G S z y (swapF G S x z e)) (lemma∙ₐc≢a∧c≢b w≠z w≠y) ⟩
         w                        , swapF G S z y (swapF G S x z e)
      ∼⟨ lemma∼+B (lemma∼swapCancelF z#e y#e) ⟩
         w                        , swapF G S x y e       
      ≈⟨ cong (λ X → X , swapF G S x y e) (sym (lemma∙ₐc≢a∧c≢b (sym≢ x≠w) w≠y)) ⟩       
        （ x ∙ y ）ₐ w             , swapF G S x y e       
      ∎
   where
   open ∼F-Reasoning(F)(|B| S G)

  lemma∼swapCancelFƛ : {F G : Functor}{S S' : Sort}{e : ⟦ G ⟧ (μ F)}{x y z : V}
                     → freshF S z (|B| S' G) (x , e)
                     → freshF S y (|B| S' G) (x , e)             
                     → ∼αF G (swapF G S z y (swapF G S x z e)) (swapF G S x y e)
  lemma∼swapCancelFƛ {F} {G} {S} {S'} {e} {x} {y} {z} z#xe y#xe 
    with S ≟S S' 
  lemma∼swapCancelFƛ                                    freshb≡       y#xe          | no S≢S' = ⊥-elim (S≢S' refl)
  lemma∼swapCancelFƛ                                    (freshb z#xe) freshb≡       | no S≢S' = ⊥-elim (S≢S' refl)
  lemma∼swapCancelFƛ                                    (freshb z#e)  (freshb y#e)  | no S≢S' = lemma∼swapCancelF z#e y#e
  lemma∼swapCancelFƛ {F} {G} {S} {.S} {e} {x} .{x} .{x} freshb≡       freshb≡       | yes refl
    = subst (λ X → ∼αF G X (swapF G S x x e)) (lemmaSwapId {F} {G}) ρF
  lemma∼swapCancelFƛ {F} {G} {S} {.S} {e} {x} {y}  .{x} freshb≡       (freshb y#e)  | yes refl
    = subst (λ X → ∼αF G (swapF G S x y X) (swapF G S x y e)) (lemmaSwapId {F} {G}) ρF
  lemma∼swapCancelFƛ {F} {G} {S} {.S} {e} {x} .{x} {z}  (freshb z#xe) freshb≡       | yes refl
    = subst₂ (λ X Y → ∼αF G X Y) (trans (lemmaSwapIdem {F} {G}) (lemmaSwapComm {F} {G})) (lemmaSwapId {F} {G}) ρF
  lemma∼swapCancelFƛ {F} {G} {S} {.S} {e} {x} {y}  {z}  (freshb z#e) (freshb y#e)   | yes refl
    = lemma∼swapCancelF z#e y#e



lemma∼#F : {F G : Functor}{S : Sort}{x : V}{e e' : ⟦ G ⟧ (μ F)}
        → ∼αF G e e'
        → freshF S x G e
        → freshF S x G e'
lemma∼#F ∼αV              x#e               = x#e
lemma∼#F ∼α1              x#e               = x#e
lemma∼#F ∼αE              x#e               = x#e
lemma∼#F (∼αEf e∼e')      (freshEf x#e)     = freshEf    (lemma∼#F e∼e' x#e)
lemma∼#F (∼αR e∼e')       (freshR x#e)      = freshR     (lemma∼#F e∼e' x#e)
lemma∼#F (∼α+₁ e∼e')      (freshinj₁ x#e)   = freshinj₁  (lemma∼#F e∼e' x#e)
lemma∼#F (∼α+₂ e∼e')      (freshinj₂ x#e)   = freshinj₂  (lemma∼#F e∼e' x#e)
lemma∼#F (∼αx e∼e' e∼e'') (freshx x#e x#e₁) = freshx     (lemma∼#F e∼e' x#e) (lemma∼#F e∼e'' x#e₁)
lemma∼#F {F} {|B| S G} {S'} {x}
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)   x#ye with  S' ≟S S 
lemma∼#F {F} {|B| S G} {.S} {x}
         (∼αB xs {.S} {.x} {z} {.G} {e} {e'} f)  freshb≡        | no S'≠S =  ⊥-elim (S'≠S refl)
lemma∼#F {F} {|B| S G} {S'} {x}
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)   (freshb x#e)   | no S'≠S 
  with χ' xs | lemmaχaux∉ xs
... | u | u∉xs
  = freshb (lemmaSwapF#≢S→ S'≠S (lemma∼#F (f u  u∉xs) (lemmaSwapF#≢S← S'≠S x#e)))
lemma∼#F {F} {|B| S G} {.S} {x}
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)      x#ye        | yes refl with x ≟v y
lemma∼#F {F} {|B| S G} {.S} {.y}
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)      x#ye        | yes refl | yes refl with y ≟v z
lemma∼#F {F} {|B| S G} {.S} {.y}
         (∼αB xs {.S} {y} {.y} {.G} {e} {e'} f)     x#ye        | yes refl | yes refl | yes refl = freshb≡           
lemma∼#F {F} {|B| S G} {.S} {.y}
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)      x#ye        | yes refl | yes refl | no y≠z         
  with χ' (y ∷ xs ++ fvF {F} {G} e) | lemmaχaux∉ (y ∷ xs ++ fvF {F} {G} e)
... | u | u∉yxs
  = freshb (lemmaSwapF#≢→  y≠z (sym≢ (b∉a∷xs→b≢a u∉yxs)) 
                           (lemma∼#F  (f u (c∉xs++ys→c∉xs (b∉a∷xs→b∉xs u∉yxs))) 
                                      (lemmaSwapF# (lemmafvF# (c∉xs++ys→c∉ys {xs = xs} (b∉a∷xs→b∉xs u∉yxs))))))
lemma∼#F {F} {|B| S G} {.S} {.y} 
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)      freshb≡     | yes refl | no y≠y = ⊥-elim (y≠y refl)
lemma∼#F {F} {|B| S G} {.S} {x} 
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)    (freshb x#e)  | yes refl | no x≠y with x ≟v z
lemma∼#F {F} {|B| S G} {.S} {x} 
         (∼αB xs {.S} {y} {.x} {.G} {e} {e'} f)   (freshb x#e)  | yes refl | no x≠y | yes refl = freshb≡
lemma∼#F {F} {|B| S G} {.S} {x} 
         (∼αB xs {.S} {y} {z} {.G} {e} {e'} f)    (freshb x#e)  | yes refl | no x≠y | no x≠z 
  with χ' (x ∷ y ∷ z ∷ xs ++ fvF {F} {G} e) | lemmaχaux∉ (x ∷ y ∷ z ∷ xs ++ fvF {F} {G} e)
... | u | u∉
  = freshb (lemmaSwapF#≢→  x≠z 
                           (sym≢ (b∉a∷xs→b≢a u∉)) 
                           (lemma∼#F (f u (c∉xs++ys→c∉xs (d∉abc∷xs→d∉xs u∉))) (lemmaSwapF#≢← x≠y (sym≢ (b∉a∷xs→b≢a u∉)) x#e)))   



lemma∼B : {F G : Functor}{S : Sort}{x y z : V}{e e′ : ⟦ G ⟧ (μ F)}
        → ∼αF (|B| S G) (x , e) (y , e′)
        → freshF S z (|B| S G) (x , e)
        → ∼αF G (swapF G S x z e) (swapF G S y z e′)
lemma∼B {F} {G} {S} {x} {y} {z} {e} {e'} (∼αB xs f) z#xe 
  with χ' (fvF {F} {|B| S G} (x , e) ++ xs) | lemmaχaux∉ (fvF {F} {|B| S G} (x , e) ++ xs)
... | u | u∉fvxe++xs  
  =  begin 
       swapF G S x z e 
     ∼⟨ σF (lemma∼swapCancelFƛ u#xe z#xe) ⟩
       swapF G S u z (swapF G S x u e)
     ∼⟨ lemma∼swapEquivF (f u (c∉xs++ys→c∉ys {xs = fvF {F} {|B| S G} (x , e)} u∉fvxe++xs)) u z ⟩
       swapF G S u z (swapF G S y u e')
     ∼⟨ lemma∼swapCancelFƛ u#ye' z#ye' ⟩
       swapF G S y z e'
     ∎ 
  where 
  open ∼F-Reasoning(F)(G)
  u#xe : freshF S u (|B| S G) (x , e)
  u#xe = lemmafvF# (c∉xs++ys→c∉xs u∉fvxe++xs)
  u#ye' : freshF S u (|B| S G) (y , e')
  u#ye' = lemma∼#F (∼αB xs f) u#xe
  z#ye' : freshF S z (|B| S G) (y , e')
  z#ye' = lemma∼#F (∼αB xs f) z#xe

lemma∼Bswap : {F G : Functor}{S : Sort}{x y : V}{e e′ : ⟦ G ⟧ (μ F)}
        → ∼αF (|B| S G) (x , e) (y , e′)
        → ∼αF G (swapF G S x y e) e′
lemma∼Bswap {F} {G} {S} {x} {y} {e} {e′} xe∼ye′
  =  begin
       swapF G S x y e
     ∼⟨ lemma∼B {x = x} {y} {y} xe∼ye′ (lemma∼#F (σF xe∼ye′) freshb≡) ⟩
       swapF G S y y e′
     ≈⟨ sym (lemmaSwapId {F} {G} {S} {y} {e′}) ⟩
       e′
     ∎
  where 
  open ∼F-Reasoning(F)(G)

lemma∼+Brec : {F G : Functor}{e e′ : ⟦ G ⟧ (μ F)}{S : Sort}{a : V} → ∼αF {F} (|B| S G) (a , e) (a , e′) → ∼αF {F} G e e′
lemma∼+Brec {F} {G} {e} {e′} {S} {a} ae~ae′
  =  begin
       e
     ≈⟨ lemmaSwapId {F} {G} {S} {a} {e} ⟩
       swapF G S a a e
     ∼⟨ lemma∼Bswap ae~ae′ ⟩
       e′
     ∎
  where 
  open ∼F-Reasoning(F)(G)

\end{code}

%<*lemafoldmapfalpha>
\begin{code}
lemma-foldmapfα  : {F H : Functor}(G : Functor)
                  {f f' : ⟦ F ⟧ (μ H) → μ H}
               →  ({e e' :  ⟦ F ⟧ (μ H)} → ∼αF F e e' → f e ∼α f' e') 
               →  (e : ⟦ G ⟧ (μ F)) → ∼αF G (foldmap F G f e) (foldmap F G f' e)
lemma-foldmapfα (|v| S)       p  e          = ∼αV
lemma-foldmapfα |1|           p  e          = ∼α1
lemma-foldmapfα {F} |R|       p  ⟨ e ⟩      
  = p     (lemma-foldmapfα F   p e)
lemma-foldmapfα (|E| x)       p  e          = ∼αE 
lemma-foldmapfα (|Ef| G)      p  e          = ρF 
lemma-foldmapfα (G₁ |+|  G₂)  p  (inj₁ e)   
  = ∼α+₁  (lemma-foldmapfα G₁  p e)
lemma-foldmapfα (G₁ |+|  G₂)  p  (inj₂ e)   
  = ∼α+₂  (lemma-foldmapfα G₂  p e)
lemma-foldmapfα (G₁ |x|  G₂)  p  (e₁ , e₂)  
  = ∼αx   (lemma-foldmapfα G₁  p e₁) 
          (lemma-foldmapfα G₂  p e₂)
lemma-foldmapfα (|B| S   G)   p  (x , e)    
  = ∼αB [] (λ y _ → lemma∼swapEquivF (lemma-foldmapfα G p e) x y)
\end{code}
%</lemafoldmapfalpha>


%<*lemma-foldfalpha>
\begin{code}
lemma-fold-alpha  : {F H : Functor}{f f' : ⟦ F ⟧ (μ H) → μ H}
              → ({e e' :  ⟦ F ⟧ (μ H)} → ∼αF F e e' → f e ∼α f' e') 
              → (e : μ F) → fold F f e ∼α fold F f' e
\end{code}
%</lemma-foldfalpha>

\begin{code}
lemma-fold-alpha {F} p e = lemma-foldmapfα |R| p e
\end{code}
-- lemma-foldmapSCtx  : {F H C : Functor}(G : Functor){f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c′ : μ C}
--               → ({e e′ :  ⟦ F ⟧ (μ H)}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)               
--               → c ∼α c′
--               → (e : ⟦ G ⟧ (μ F)) → ∼αF G (foldmapCtx F G f c e) (foldmapCtx F G f c′ e)
-- lemma-foldmapSCtx (|v| S)      prf c∼c′  e          = ∼αV
-- lemma-foldmapSCtx |1|          prf c∼c′  e          = ∼α1
-- lemma-foldmapSCtx {F} |R|      prf c∼c′  ⟨ e ⟩      = prf c∼c′ (lemma-foldmapSCtx F prf c∼c′ e)
-- lemma-foldmapSCtx (|E| x)      prf c∼c′  e          = ∼αE 
-- lemma-foldmapSCtx (|Ef| G)     prf c∼c′  e          = ρF 
-- lemma-foldmapSCtx (G₁ |+| G₂)  prf c∼c′  (inj₁ e)   = ∼α+₁  (lemma-foldmapSCtx G₁ prf c∼c′  e)
-- lemma-foldmapSCtx (G₁ |+| G₂)  prf c∼c′  (inj₂ e)   = ∼α+₂  (lemma-foldmapSCtx G₂ prf c∼c′  e)
-- lemma-foldmapSCtx (G₁ |x| G₂)  prf c∼c′  (e₁ , e₂)  = ∼αx   (lemma-foldmapSCtx G₁ prf c∼c′  e₁) (lemma-foldmapSCtx G₂ prf c∼c′  e₂)
-- lemma-foldmapSCtx (|B| S G)    prf c∼c′  (x , e)    = ∼αB   [] (λ y y∉[] → lemma∼swapEquivF (lemma-foldmapSCtx G prf c∼c′  e) x y)


%<*lemmafoldCtxalphactx>
\begin{code}
lemma-foldCtx-alpha-Ctx  : {F H C : Functor}{f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c′ : μ C}
  →  ({e e′ :  ⟦ F ⟧ (μ H)}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)          
  →  c ∼α c′ →  (e : μ F) → foldCtx F f c e ∼α foldCtx F f c′ e
lemma-foldCtx-alpha-Ctx {F} {f = f} {c} {c′} p c∼c′ e = lemma-fold-alpha (p c∼c′) e  
\end{code}
%</lemmafoldCtxalphactx>

\begin{code}
lemma-B# : {F G : Functor}{S : Sort}{x y : V}{e : ⟦ G ⟧ (μ F) } → freshF S y G e → ∼αF (|B| S G) (y , swapF G S x y e)  (x , e)
lemma-B# {F} {G} {S} {x} {y} {e} y#e
  = ∼αB (fvSF {F} {G} S e) (λ z z∉fve →
       begin
         swapF G S y z (swapF G S x y e)
       ∼⟨ lemma∼swapCancelF {F} {G} {S} {e} y#e (lemmafvSF# {F} {G} {z} {S} {e} z∉fve) ⟩
         swapF G S x z e
       ∎)
  where 
  open ∼F-Reasoning(F)(G)

lemma-B#' : {F G : Functor}{S : Sort}{x y : V}{e : ⟦ G ⟧ (μ F) } → freshF S y G e → ∼αF (|B| S G) (y , swapF G S y x e) (x , e)
lemma-B#' {F} {G} {S} {x} {y} {e} y#e
  =  begin
       y , swapF G S y x e
     ≈⟨ cong₂ (_,_) refl (lemmaSwapComm {F} {G} {S} {y} {x} {e}) ⟩
       y , swapF G S x y e
     ∼⟨ lemma-B# y#e ⟩
       x , e
     ∎
  where 
  open ∼F-Reasoning(F)(|B| S G)
  
lemma-swap#F : {F G : Functor}{S : Sort}{x y : V}{e : ⟦ G ⟧ (μ F) } → freshF S x G e → freshF S y G e → ∼αF G (swapF G S x y e)  e
lemma-swap#F {F} {|1|}      {S} {x} {y} {e}        x#e                 y#e                 = ∼α1
lemma-swap#F {F} {|R|}      {S} {x} {y} {⟨ e ⟩}    (freshR x#e)        (freshR y#e)        = ∼αR (lemma-swap#F x#e y#e)
lemma-swap#F {F} {|E| A}    {S} {x} {y} {e}        x#e                 y#e                 = ∼αE
lemma-swap#F {F} {|Ef| G}   {S} {x} {y} {⟨ e ⟩}    (freshEf x#e)       (freshEf y#e)       = ∼αEf (lemma-swap#F x#e y#e)
lemma-swap#F {F} {G |+| G₁} {S} {x} {y} {inj₁ e}   (freshinj₁ x#e)     (freshinj₁ y#e)     = ∼α+₁ (lemma-swap#F x#e y#e)
lemma-swap#F {F} {G |+| G₁} {S} {x} {y} {inj₂ e}   (freshinj₂ x#e)     (freshinj₂ y#e)     = ∼α+₂ (lemma-swap#F x#e y#e)
lemma-swap#F {F} {G |x| G₁} {S} {x} {y} {e₁ , e₂}  (freshx x#e₁ x#e₂)  (freshx y#e₁ y#e₂)  = ∼αx (lemma-swap#F x#e₁ y#e₁) (lemma-swap#F x#e₂ y#e₂)
lemma-swap#F {F} {|v| S′}   {S} {x} {y} {z}        x#e                 y#e
  with swapF {F} (|v| S′) S x y z | lemmaSwap#Var {F} x#e y#e
... | .z | refl                                                                            = ∼αV 
lemma-swap#F {F} {|B| S′ G} {S} {x} {y} {z , e}    x#e                 y#e
  with S′ ≟S S
lemma-swap#F {F} {|B| S G}  {.S} {.z} {y} {z , e}  freshb≡ y#e                      | no S≢S   = ⊥-elim (S≢S refl)
lemma-swap#F {F} {|B| S G}  {.S} {x} {.z} {z , e}  (freshb x#e)        freshb≡      | no S≢S   = ⊥-elim (S≢S refl)
lemma-swap#F {F} {|B| S′ G} {S}  {x} {y} {z , e}   (freshb x#e)        (freshb y#e) | no _     = lemma∼+B (lemma-swap#F x#e y#e)
lemma-swap#F {F} {|B| S G} {.S} {.z} {.z} {z , e}  freshb≡             freshb≡      | yes refl
  =  begin
       （ z ∙ z ）ₐ z , swapF G S z z e
     ≈⟨ cong₂ (_,_) lemma（aa）b≡b refl ⟩
        z , swapF G S z z e
     ≈⟨ cong₂ (_,_) refl (sym (lemmaSwapId {F} {G} {S} {z} {e})) ⟩ 
        z , e
     ∎
  where 
  open ∼F-Reasoning(F)(|B| S G)
lemma-swap#F {F} {|B| S G} {.S} {.z} {y} {z , e}   freshb≡             (freshb y#e) | yes refl
  with （ z ∙ y ）ₐ z | lemma（ab）a≡b {z} {y}
... |   .y  | refl = lemma-B#  y#e
lemma-swap#F {F} {|B| S G} {.S} {x} {.z} {z , e}   (freshb x#e)        freshb≡      | yes refl
  with （ x ∙ z ）ₐ z | lemma（ab）b≡a {x} {z}
... |   .x  | refl = lemma-B#'  x#e
lemma-swap#F {F} {|B| S G} {.S} {x} {y} {z , e}    (freshb x#e)        (freshb y#e) | yes refl
  with （ x ∙ y ）ₐ z | lemma∙ₐ x y z
lemma-swap#F {F} {|B| S G} {.S} {x} {y} {.x , e}    (freshb x#e)        (freshb y#e) | yes refl  
  | .y | inj₁ (refl , refl)               = lemma-B# y#e
lemma-swap#F {F} {|B| S G} {.S} {x} {y} {.y , e}    (freshb x#e)        (freshb y#e) | yes refl 
  | .x | inj₂ (inj₁ (refl , z≢x , refl))  = lemma-B#' x#e
lemma-swap#F {F} {|B| S G} {.S} {x} {y} {z , e}    (freshb x#e)        (freshb y#e) | yes refl  
  | .z | inj₂ (inj₂ (z≢x  , z≢y , refl))  = lemma∼+B (lemma-swap#F x#e y#e)
    
lemma-swap# : {F : Functor}{S : Sort}{x y : V}{e : μ F} → fresh S x e → fresh S y e → swap S x y e ∼α e
lemma-swap# {F} = lemma-swap#F {F} {|R|}

lemma-swapListNotOccurBind : {F G : Functor}{S : Sort}{x y : V}{e : ⟦ G ⟧ (μ F)}{xs : List V}
                          → x ∉ xs → y ∉ xs
                          → ListNotOccurBindF G xs e
                          → ListNotOccurBindF G xs (swapF G S y x e)
lemma-swapListNotOccurBind {F} {|1|}      {S} {x} {y} {e}       x∉xs y∉ys xs∉be = lemma-binds1
lemma-swapListNotOccurBind {F} {|R|}      {S} {x} {y} {⟨ e ⟩}   x∉xs y∉ys xs∉be = lemma-bindsR (lemma-swapListNotOccurBind x∉xs y∉ys (lemmalistNotOccurBindFR→ListNotOccurBindF xs∉be))
lemma-swapListNotOccurBind {F} {|E| _}    {S} {x} {y} {e}       x∉xs y∉ys xs∉be = lemma-bindsE
lemma-swapListNotOccurBind {F} {|Ef| G}   {S} {x} {y} {⟨ e ⟩}   x∉xs y∉ys xs∉be = lemma-bindsEf (lemma-swapListNotOccurBind x∉xs y∉ys (lemmalistNotOccurBindEf→ListNotOccurBindF xs∉be))
lemma-swapListNotOccurBind {F} {G |+| G₁} {S} {x} {y} {inj₁ e}  x∉xs y∉ys xs∉be = lemma-binds+1 (lemma-swapListNotOccurBind x∉xs y∉ys (listNotOccurBinj₁inv xs∉be))
lemma-swapListNotOccurBind {F} {G |+| G₁} {S} {x} {y} {inj₂ e}  x∉xs y∉ys xs∉be = lemma-binds+2 (lemma-swapListNotOccurBind x∉xs y∉ys (listNotOccurBinj₂inv xs∉be))
lemma-swapListNotOccurBind {F} {G |x| G₁} {S} {x} {y} {e₁ , e₂} x∉xs y∉ys xs∉be = lemma-binds× (lemma-swapListNotOccurBind x∉xs y∉ys (listNotOccurBx₁inv xs∉be)) ((lemma-swapListNotOccurBind x∉xs y∉ys (listNotOccurBx₂inv xs∉be)))
lemma-swapListNotOccurBind {F} {|v| x}    {S} {x₁} {y} {e}      x∉xs y∉ys xs∉be = lemma-bindsv
lemma-swapListNotOccurBind {F} {|B| S′ G} {S} {x} {y} {z , e}   x∉xs y∉ys xs∉be with S′ ≟S S
... | yes _ = lemma-bindsB (lemma∉swap y∉ys x∉xs (listNotOccurBBinv∉fv xs∉be)) (lemma-swapListNotOccurBind x∉xs y∉ys (listNotOccurBBinv xs∉be))
... | no  _ = lemma-bindsB (listNotOccurBBinv∉fv xs∉be) (lemma-swapListNotOccurBind x∉xs y∉ys (listNotOccurBBinv xs∉be))

-- lemma-foldmapα  : {F H C : Functor}(G : Functor){f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c' : μ C}{e e' : ⟦ G ⟧ (μ F)}
--                → ({e e′ :  ⟦ F ⟧ (μ H)}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
--                → ({c : μ C}{S : Sort}{x y : V}{e : ⟦ F ⟧ (μ H)} → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
--                → ListNotOccurBindF G (fv c)   e
--                → ListNotOccurBindF G (fv c')  e'
--                → c ∼α c'
--                → ∼αF G e e'  
--                → ∼αF G (foldmapCtx F G f c e) (foldmapCtx F G f c' e')
-- lemma-foldmapα (|v| S)        prf _ nb nb' _    ∼αV         = ∼αV  
-- lemma-foldmapα |1|            prf _ nb nb' _    ∼α1         = ∼α1 
-- lemma-foldmapα {F} |R|        prf prf2  nb nb' c∼c' (∼αR e∼e')
--   = prf c∼c' (lemma-foldmapα F prf prf2 (lemmalistNotOccurBindFR→ListNotOccurBindF nb) (lemmalistNotOccurBindFR→ListNotOccurBindF nb') c∼c' e∼e')  
-- lemma-foldmapα (|E| x)        prf _ nb nb' _    ∼αE         = ρF 
-- lemma-foldmapα (|Ef| G)       prf _ nb nb' _    (∼αEf e∼e') = ∼αEf e∼e'
-- lemma-foldmapα (G₁ |+| G₂)    prf prf2 nb nb' c∼c' (∼α+₁ e∼e')
--   = ∼α+₁  (lemma-foldmapα G₁ prf prf2 (listNotOccurBinj₁inv nb) (listNotOccurBinj₁inv nb') c∼c' e∼e')  
-- lemma-foldmapα (G₁ |+| G₂)    prf prf2 nb nb' c∼c' (∼α+₂ e∼e')
--   = ∼α+₂  (lemma-foldmapα G₂ prf prf2 (listNotOccurBinj₂inv nb) (listNotOccurBinj₂inv nb') c∼c' e∼e') 
-- lemma-foldmapα (G₁ |x| G₂)    prf prf2 nb nb' c∼c' (∼αx α₁ α₂)
--   = ∼αx   (lemma-foldmapα G₁ prf prf2 (listNotOccurBx₁inv nb) (listNotOccurBx₁inv nb') c∼c' α₁)
--           (lemma-foldmapα G₂ prf prf2 (listNotOccurBx₂inv nb) (listNotOccurBx₂inv nb') c∼c' α₂)  
-- lemma-foldmapα {F} {H} {C} (|B| S G) {f} {c} {c'}  {y , e} {z , e'}
--                prf prf2 nb nb' c∼c' (∼αB xs fα)  
--   = ∼αB  (fv c ++ fv c' ++ xs)
--          (λ x x∉ → begin
--                      swapF G S y x (foldmapCtx F G f c e)
--                    ≈⟨ sym (lemmaSwapFoldSEquivF {C} {H} {F} {G} prf2)  ⟩
--                      foldmapCtx F G f (swap S y x c) (swapF G S y x e)
--                    ∼⟨ lemma-foldmapSCtx G prf
--                                         (lemma-swap# (lemmafvF# (listNotOccurBBinv∉fv nb)) (lemmafvF# (c∉xs++ys→c∉xs x∉)))
--                                         (swapF G S y x e) ⟩
--                      foldmapCtx F G f c              (swapF G S y x e)
--                    ∼⟨ lemma-foldmapα  G prf prf2
--                                       (lemma-swapListNotOccurBind (c∉xs++ys→c∉xs x∉) (listNotOccurBBinv∉fv nb) (listNotOccurBBinv nb))
--                                       (lemma-swapListNotOccurBind (c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = fv c} x∉)) (listNotOccurBBinv∉fv nb') (listNotOccurBBinv nb'))
--                                       c∼c'
--                                       (fα x (c∉xs++ys→c∉ys {xs = fv c'} (c∉xs++ys→c∉ys {xs = fv c} x∉))) ⟩
--                      foldmapCtx F G f c'             (swapF G S z x e')
--                    ∼⟨ lemma-foldmapSCtx  G prf (σ (lemma-swap#  (lemmafvF# (listNotOccurBBinv∉fv nb'))
--                                                                 (lemmafvF# (c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = fv c} x∉)))))
--                                          (swapF G S z x e') ⟩
--                      foldmapCtx F G f (swap S z x c') (swapF G S z x e')
--                    ≈⟨ lemmaSwapFoldSEquivF {C} {H} {F} {G} prf2 ⟩
--                      swapF G S z x (foldmapCtx F G f c' e')
--                    ∎)
--      where
--      open ∼F-Reasoning(H)(G)
  
lemma-foldmapα  : {F H C : Functor}(G : Functor)
     {f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c' : μ C}{e e' : ⟦ G ⟧ (μ F)}
  →  ({e e′ :  ⟦ F ⟧ (μ H)}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
  →  ({c : μ C}{S : Sort}{x y : V}{e : ⟦ F ⟧ (μ H)} →
                 f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
  →  ListNotOccurBindF G (fv c)   e
  →  ListNotOccurBindF G (fv c')  e'
  →  c ∼α c'  → ∼αF G e e'  
  →  ∼αF G (foldmap F G (f c) e) (foldmap F G (f c') e')
lemma-foldmapα (|v| S)        prf _ nb nb' _    ∼αV         = ∼αV  
lemma-foldmapα |1|            prf _ nb nb' _    ∼α1         = ∼α1 
lemma-foldmapα {F} |R|        prf prf2  nb nb' c∼c' (∼αR e∼e')
  = prf c∼c' (lemma-foldmapα F prf prf2 (lemmalistNotOccurBindFR→ListNotOccurBindF nb) (lemmalistNotOccurBindFR→ListNotOccurBindF nb') c∼c' e∼e')  
lemma-foldmapα (|E| x)        prf _ nb nb' _    ∼αE         = ρF 
lemma-foldmapα (|Ef| G)       prf _ nb nb' _    (∼αEf e∼e') = ∼αEf e∼e'
lemma-foldmapα (G₁ |+| G₂)    prf prf2 nb nb' c∼c' (∼α+₁ e∼e')
  = ∼α+₁  (lemma-foldmapα G₁ prf prf2 (listNotOccurBinj₁inv nb) (listNotOccurBinj₁inv nb') c∼c' e∼e')  
lemma-foldmapα (G₁ |+| G₂)    prf prf2 nb nb' c∼c' (∼α+₂ e∼e')
  = ∼α+₂  (lemma-foldmapα G₂ prf prf2 (listNotOccurBinj₂inv nb) (listNotOccurBinj₂inv nb') c∼c' e∼e') 
lemma-foldmapα (G₁ |x| G₂)    prf prf2 nb nb' c∼c' (∼αx α₁ α₂)
  = ∼αx   (lemma-foldmapα G₁ prf prf2 (listNotOccurBx₁inv nb) (listNotOccurBx₁inv nb') c∼c' α₁)
          (lemma-foldmapα G₂ prf prf2 (listNotOccurBx₂inv nb) (listNotOccurBx₂inv nb') c∼c' α₂)  
lemma-foldmapα {F} {H} {C} (|B| S G) {f} {c} {c'}  {y , e} {z , e'}
               prf prf2 nb nb' c∼c' (∼αB xs fα)  
  = ∼αB  (fv c ++ fv c' ++ xs)
         (λ x x∉ → begin
                     swapF G S y x (foldmap F G (f c) e)
                   ≈⟨ sym (lemmaSwapFoldEquivCtxF {F} {G} {H} {f = λ y x → f (swap S y x c)} {g = f c} prf2)  ⟩
                     foldmap F G (f (swap S y x c))   (swapF G S y x e)
                   ∼⟨ lemma-foldmapfα G (prf (lemma-swap# (lemmafvF# (listNotOccurBBinv∉fv nb)) (lemmafvF# (c∉xs++ys→c∉xs x∉)))) (swapF G S y x e) ⟩
                     foldmap F G (f c)                (swapF G S y x e)
                   ∼⟨ lemma-foldmapα  G prf prf2
                                      (lemma-swapListNotOccurBind (c∉xs++ys→c∉xs x∉) (listNotOccurBBinv∉fv nb) (listNotOccurBBinv nb))
                                      (lemma-swapListNotOccurBind (c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = fv c} x∉)) (listNotOccurBBinv∉fv nb') (listNotOccurBBinv nb'))
                                      c∼c'
                                      (fα x (c∉xs++ys→c∉ys {xs = fv c'} (c∉xs++ys→c∉ys {xs = fv c} x∉))) ⟩
                     foldmap F G (f c')               (swapF G S z x e')
                   ∼⟨ lemma-foldmapfα G  (prf (σ (lemma-swap#  (lemmafvF# (listNotOccurBBinv∉fv nb'))
                                                               (lemmafvF# (c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = fv c} x∉)))))) 
                                         (swapF G S z x e')  ⟩
                     foldmap F G (f (swap S z x c'))  (swapF G S z x e')
                   ≈⟨ lemmaSwapFoldEquivCtxF {F} {G} {H} {f = λ z x → f (swap S z x c')} {g = f c'} prf2  ⟩
                     swapF G S z x (foldmap F G (f c') e')
                   ∎)
     where
     open ∼F-Reasoning(H)(G)
\end{code}

%<*lemmafoldCtxalpha>
\begin{code}
lemma-foldCtx-alpha  : {F H C : Functor}{f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c' : μ C}{e e' : μ F}
  →  ({e e′ :  ⟦ F ⟧ (μ H)}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
  → ({c : μ C}{S : Sort}{x y : V}{e : ⟦ F ⟧ (μ H)}
              → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
  → ListNotOccurBind (fv c)   e → ListNotOccurBind (fv c')  e'
  → c ∼α c' → e ∼α e' → foldCtx F f c e ∼α foldCtx F f c' e'
\end{code}
%</lemmafoldCtxalpha>

\begin{code}
lemma-foldCtx-alpha prf prf2 nb nb' c∼c' e∼e' = lemma-foldmapα |R| prf prf2 nb nb' c∼c' e∼e' 
\end{code}

\begin{code}
mutual
  lemmafvα : {F G : Functor}{S : Sort}{e e′ : ⟦ G ⟧ (μ F)}
       → ∼αF {F} G e e′
       → fvSF {F} {G} S e ≡ fvSF {F} {G} S e′
  lemmafvα {F} {|1|}       {S} {e}        {e′}         e~e′        = refl
  lemmafvα {F} {|R|}       {S} {⟨ e ⟩}    {⟨ e′ ⟩}     (∼αR e~e′)  = lemmafvα {F} {F} {S} {e} {e′} e~e′
  lemmafvα {F} {|E| x}     {S} {e}        {e′}         e~e′        = refl
  lemmafvα {F} {|Ef| G}    {S} {⟨ e ⟩}    {⟨ e′ ⟩}     (∼αEf e~e′) = lemmafvα {G} {G} {S} {e} {e′} e~e′
  lemmafvα {F} {G₁ |+| G₂} {S} {inj₁ e}   {inj₁ e′}    (∼α+₁ e~e′) = lemmafvα {F} {G₁} {S} {e} {e′} e~e′
  lemmafvα {F} {G₁ |+| G₂} {S} {inj₂ e}   {inj₂ e′}    (∼α+₂ e~e′) = lemmafvα {F} {G₂} {S} {e} {e′} e~e′
  lemmafvα {F} {G₁ |x| G₂} {S} {e₁ , e₂}  {e₁′ , e₂′}  (∼αx e₁~e₁′ e₂~e₂′)
    = cong₂ (_++_) (lemmafvα {F} {G₁} {S} {e₁} {e₁′} e₁~e₁′) (lemmafvα {F} {G₂} {S} {e₂} {e₂′} e₂~e₂′)
  lemmafvα {F} {|v| S′}    {S} {e}      {.e}            ∼αV         =  refl
  lemmafvα {F} {|B| S′ G}  {S} {x , e}  {y , e′}        xe∼ye′ with S′ ≟S S
  ... | no S′≢S   = lemmafvswapBF≢ S′≢S xe∼ye′
  lemmafvα {F} {|B| .S G}  {S} {x , e}  {y , e′}        xe∼ye′ 
      | yes refl  = lemmafvswapBF xe∼ye′

  lemmafvswapBF≢ : {F G : Functor}{x y : V}{S S′ : Sort}{e e′ : ⟦ G ⟧ (μ F)}
             → S′ ≢ S 
             → ∼αF {F} (|B| S′ G) (x , e) (y , e′)
             → fvSF {F} {G} S e ≡ fvSF {F} {G} S e′
  lemmafvswapBF≢ {F} {G} {x} {y} {S} {S′} {e} {e′} S′≢S xe~ye′ = 
    begin≡
      fvSF {F} {G} S e
    ≡⟨ lemma-swapfvSF {F} {G} {e} {S′} {S} (sym≢ S′≢S) ⟩
      fvSF {F} {G} S (swapF G S′ x y e)
    ≡⟨ lemmafvα {F} {G} {S} (lemma∼Bswap {F} {G} {S′} {x} {y} xe~ye′) ⟩
      fvSF {F} {G} S e′
    □
  
  lemmafvswapBF : {F G : Functor}{x y : V}{S : Sort}{e e′ : ⟦ G ⟧ (μ F)} 
             → ∼αF {F} (|B| S G) (x , e) (y , e′)
             → fvSF {F} {G} S e - x ≡ fvSF {F} {G} S e′ - y 
  lemmafvswapBF {F} {G} {x} {y}   {S} {e} {e′} ∼αBxeye′ with lemma∼#F {F} {(|B| S G)} {S} {y} {y , e′} {x , e} (σF ∼αBxeye′) freshb≡
  lemmafvswapBF {F} {G} {x} {.x}  {S} {e} {e′} ∼αBxeye′ | freshb≡    = 
    begin≡
      fvSF {F} {G} S e  - x
    ≡⟨ cong (λ e → e - x) (lemmafvα {F} {G} {S} {e} {e′} (lemma∼+Brec ∼αBxeye′)) ⟩
    fvSF {F} {G} S e′ - x
    □
  lemmafvswapBF {F} {G} {x} {y}   {S} {e} {e′} ∼αBxeye′ | freshb y#e = 
    begin≡
      fvSF {F} {G} S e - x
    ≡⟨ lemmafvswap- {F} {G} {x} {y} {S} {e} y#e ⟩
    fvSF {F} {G} S (swapF G S x y e) - y
    ≡⟨ cong₂ (_-_) {u = y} (lemmafvα (lemma∼Bswap {F} {G} {S} {x} {y} ∼αBxeye′)) refl  ⟩     
    fvSF {F} {G} S e′ - y
    □

lemma∼fvF :  {F G : Functor}{e e′ : ⟦ G ⟧ (μ F)}
             (xs : List V) 
             → ∼αF G e e′
             → fvSF≢ {F} {G} xs e ≡ fvSF≢ {F} {G} xs e′
lemma∼fvF {F} {|1|}       {e}          {e′}        _  e~e′                 = refl
lemma∼fvF {F} {|R|}       {⟨ e ⟩}      {⟨ e′ ⟩}    xs (∼αR e~e′)           = lemma∼fvF xs e~e′
lemma∼fvF {F} {|E| x}     {e}          {e′}        _  e~e′                 = refl
lemma∼fvF {F} {|Ef| G}    {⟨ e ⟩}      {⟨ e′ ⟩}    xs (∼αEf e~e′)          = lemma∼fvF xs e~e′
lemma∼fvF {F} {G |+| G₁}  {.(inj₁ _)}  {.(inj₁ _)} xs (∼α+₁ e~e′)          = lemma∼fvF xs e~e′
lemma∼fvF {F} {G |+| G₁}  {.(inj₂ _)}  {.(inj₂ _)} xs (∼α+₂ e~e′)          = lemma∼fvF xs e~e′
lemma∼fvF {F} {G |x| G₁}  {e₁ , e₁′}   {e₂ , e₂′}  xs (∼αx e₁~e₁′ e₂~e₂′)  = cong₂ (_++_) (lemma∼fvF xs e₁~e₁′) (lemma∼fvF xs e₂~e₂′)
lemma∼fvF {F} {|v| S}     {e}          {.e}        _  ∼αV                  = refl
lemma∼fvF {F} {|B| S G}   {x , e}      {y , e′}    xs ∼αBxeye′ with any (_≟S_ S) xs
... | yes S∈xs = 
   begin≡
     fvSF≢ {F} {G} xs e
   ≡⟨ lemma-swapfvF {F} {G} {e} {S} {x} {y} {xs} S∈xs  ⟩
     fvSF≢ {F} {G} xs (swapF G S x y e)
   ≡⟨ lemma∼fvF {F} {G} {swapF G S x y e} {e′} xs (lemma∼Bswap {F} {G} {S} {x} {y} ∼αBxeye′) ⟩
     fvSF≢ {F} {G} xs e′
   □  
... | no  S∉xs = cong₂ (_++_)
   (begin≡ -- analogous to previous proof
     fvSF≢ {F} {G} (S ∷ xs) e
   ≡⟨ lemma-swapfvF {F} {G} {e} {S} {x} {y} {S ∷ xs} (here refl)  ⟩
     fvSF≢ {F} {G} (S ∷ xs) (swapF G S x y e)
   ≡⟨ lemma∼fvF {F} {G} {swapF G S x y e} {e′} (S ∷ xs) (lemma∼Bswap {F} {G} {S} {x} {y} ∼αBxeye′) ⟩
     fvSF≢ {F} {G} (S ∷ xs) e′
   □)
   (lemmafvswapBF {F} {G} {x} {y} {S} {e} {e′} ∼αBxeye′)

lemma∼fv :  {F : Functor}{e e' : μ F}
            → e ∼α e'
            → fv e ≡ fv e'
lemma∼fv = lemma∼fvF []

  --lemmafv-∉ : {F : Functor}{S : Sort}{e : ⟦ F ⟧ (μ F)}{x y : V} → x ≢ y → x ∉ fvF {|B| S F} S (y , e) → x ∉ fv {F} S ⟨ e ⟩
  -- lemma-foldSfv : {C H : Functor}{F : Functor}{f : μ C → ⟦ F ⟧ (μ H) → μ H}{c : μ C}{e : μ F}{S : Sort}
  --                 → fv (foldS F f c e) ⊆ fv c ++ fv e
  
\end{code}
