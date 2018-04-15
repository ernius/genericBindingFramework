\begin{code}
module FreeVariables where

open import GPBindings
open import Fresh
open import List.ListProperties
open import Swap
open import SwapInduction
open import Chi

open import Function
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product hiding (swap)
open import Data.List hiding (any)
open import Data.Bool
open import Relation.Nullary.Decidable hiding (map)
open import Data.List.Any as any
open any.Membership-≡
open import Relation.Binary.PropositionalEquality hiding ([_])
\end{code}

Why not implemented with fold ? Because as swap must transverse |Ef|

%<*freevariables>
\begin{code}
fvSF : {F G : Functor} → Sort → ⟦ G ⟧ (μ F) → List V  
fvSF {F} {|v| S'}   S e with S' ≟S  S
... | yes _                      = [ e ]
... | no  _                      = []
fvSF {F} {|1|}        S tt       = []
fvSF {F} {|E| x}      S e        = []
fvSF {F} {|Ef|   G}   S ⟨ e ⟩    = fvSF {G} {G} S e
fvSF {F} {|R|}        S ⟨ e ⟩    = fvSF {F} {F} S e
fvSF {F} {G₁ |+| G₂}  S (inj₁ x) = fvSF {F} {G₁} S x
fvSF {F} {G₁ |+| G₂}  S (inj₂ y) = fvSF {F} {G₂} S y
fvSF {F} {G₁ |x| G₂}  S (x , y)  = fvSF {F} {G₁} S x ++ fvSF {F} {G₂} S y
fvSF {F} {|B| S' G}   S (x , e) with S' ≟S  S
... | yes _                      = fvSF {F} {G} S e - x
... | no  _                      = fvSF {F} {G} S e

fvS : {F : Functor} → Sort → μ F → List V
fvS {F} S e = fvSF {F} {|R|} S e 
\end{code}
%</freevariables>

\begin{code}  
-- fvcases : (F : Functor)(S : Sort) → ⟦ F ⟧ (List V) → List V
-- fvcases (|v| S') S x with S' ≟S  S
-- ... | yes _     = [ x ]
-- ... | no  _     = []
-- fvcases |1| S x = []
-- fvcases |R| S R = R
-- fvcases (|E| x) S _ =  []
-- fvcases (|Ef| F) S R = {!R!} -- why not implemented with fold ? because of this case !!!
-- fvcases (F |+| F₁) S x = {!!}
-- fvcases (F |x| F₁) S x = {!!}
-- fvcases (|B| x F) S x₁ = {!!}

-- fv2 : {F : Functor} → Sort → μ F → List V
-- fv2 {F} S e = fold F (fvcases F S) e


lemmafvSF# : {F G : Functor}{x : V}{S : Sort}{e : ⟦ G ⟧ (μ F)} → x ∉ (fvSF {F} {G} S e) → freshF S x G e
lemmafvSF# {F} {|v| S'}    {x = e'} {S = S}   
                      {e}          x∉fv with S' ≟S  S
... | no  S'≢S                        = freshV≢S  S'≢S
lemmafvSF# {F}  {|v| S}     {x = e'} {S = .S}
                      {e}          x∉fv
    | yes refl                        with e' ≟v  e
... | no  e'≢e                        = freshV≢ e'≢e
lemmafvSF# {F} {|v| S}     {x = .e} {S = .S}
                      {e}          x∉[x]
    | yes refl                        
    | yes refl                        = ⊥-elim (lemmax∉[x]absurd x∉[x])
lemmafvSF# {F} {|1|}       {e = tt}         x∉fv = fresh1
lemmafvSF# {F} {|E| x}     {e = e}          x∉fv = freshE
lemmafvSF# {F} {|Ef| G}    {e = ⟨ e ⟩}      x∉fv = freshEf   (lemmafvSF# x∉fv)
lemmafvSF# {F} {|R|}       {e = ⟨ e ⟩}      x∉fv = freshR    (lemmafvSF# x∉fv)
lemmafvSF# {F} {G |+| G₁}  {e = inj₁ e}     x∉fv = freshinj₁ (lemmafvSF# x∉fv)
lemmafvSF# {F} {G |+| G₁}  {e = inj₂ e}     x∉fv = freshinj₂ (lemmafvSF# x∉fv)
lemmafvSF# {F} {G |x| G₁}  {S = S}
                           {e = e₁ , e₂}    x∉fv = freshx    (lemmafvSF# (c∉xs++ys→c∉xs x∉fv))
                                                             (lemmafvSF# (c∉xs++ys→c∉ys {xs = fvSF {F} {G} S e₁} x∉fv))
lemmafvSF# {F} {|B| S' G}  {S = S}
                           {e = a , e}      x∉fv with S' ≟S  S
... | no  S'≢S                                   = freshb    (lemmafvSF# x∉fv)
lemmafvSF# {F} {|B| .S G}  {x = b} {S = S}  
                           {e = a , e}      b∉fv
    | yes refl                        with a ≟v b
... | no a≢b                                     = freshb    (lemmafvSF# (lemma-∉ a≢b b∉fv))
lemmafvSF# {F} {|B| .S G}  {x = .a} {S = S}  
                      {a , e}          a∉fv
    | yes refl                       
    | yes refl                                   = freshb≡

lemmafvS# :  {F : Functor}{x : V}{S : Sort}{e : μ F}
            → x ∉ fvS S e
            → fresh S x e
lemmafvS# {e = ⟨ e ⟩} = lemmafvSF#

lemmaS#fvF :  {F G : Functor}{e : ⟦ G ⟧ (μ F)}{S : Sort}{x : V} 
              → freshF S x G e → x ∉ fvSF {F} {G} S e
lemmaS#fvF {G = |1|}                            fresh1                 ()
lemmaS#fvF {G = |R|}                            (freshR fresh)         x∈ = lemmaS#fvF fresh x∈
lemmaS#fvF {G = |E| x}                          freshE                 ()
lemmaS#fvF {G = |Ef| G}                         (freshEf fresh)        x∈ = lemmaS#fvF fresh x∈
lemmaS#fvF {G = G₁ |+| G₂}                      (freshinj₁ fresh)      x∈ = lemmaS#fvF fresh x∈
lemmaS#fvF {G = G₁ |+| G₂}                      (freshinj₂ fresh)      x∈ = lemmaS#fvF fresh x∈
lemmaS#fvF {G = G₁ |x| G₂}  {e₁ , e₂} {S} {x}   (freshx fresh₁ fresh₂) x∈ with c∈xs++ys→c∈xs∨c∈ys {x} {fvSF {G = G₁} S e₁} {fvSF {G = G₂} S e₂} x∈
... | inj₁ x∈₁                                                            = lemmaS#fvF fresh₁ x∈₁
... | inj₂ x∈₂                                                            = lemmaS#fvF fresh₂ x∈₂
lemmaS#fvF {G = |v| S'}     {y}       {S}       (freshV≢ x≢y)          x∈ with S' ≟S S
lemmaS#fvF {G = |v| .S}     {y}       {S}       (freshV≢ x≢y)          x∈ 
    | yes refl                                                            = x≢y (lemmay∈[x]y≡x x∈)
lemmaS#fvF {G = |v| S'}     {y}       {S}       (freshV≢ x≢y)          () 
    | no  S'≢S 
lemmaS#fvF {G = |v| S'}     {y}       {S}       (freshV≢S S'≢S)        x∈ with S' ≟S S
... | yes S'≡S                                                            = ⊥-elim (S'≢S S'≡S)
lemmaS#fvF {G = |v| S'}     {y}       {S}       (freshV≢S S'≢S)        () 
    | no  _                                                           
lemmaS#fvF {G = |B| S G}    {.x , e}  {.S} {x}  freshb≡               x∈ with S ≟S S
... | yes _                                                               = lemma- {x} {fvSF {G = G} S e} x∈ 
... | no  S≢S                                                             = ⊥-elim (S≢S refl)
lemmaS#fvF {G = |B| S' G}   {y , e}   {S}  {x}  (freshb fresh)        x∈  with S' ≟S S
... | no S'≢S                                                             = lemmaS#fvF fresh x∈
lemmaS#fvF {G = |B| .S G}   {y , e}   {S}  {x}  (freshb fresh)        x∈  
    | yes refl with x ≟v y
...            | no  x≢y                                                  = lemmaS#fvF fresh (lemma-∈ {x} {y} x∈)
lemmaS#fvF {G = |B| .S G}   {.x , e}  {S}  {x}  (freshb fresh)        x∈  
    | yes refl | yes refl                                                 = lemma- {x} {fvSF {G = G} S e} x∈

-- lemmafvSwap :  {F G : Functor}{e : ⟦ G ⟧ (μ F)}{S S' : Sort}{x y : V}
--                → S' ≢ S
--                → fvF {G} {F} S (swapF F G  S' x y e) ≡ fvF {G} {F} S e
-- lemmafvSwap = {!!}

-- lemma~fv :  {F G : Functor}{e e′ : ⟦ G ⟧ (μ F)}(S : Sort)
--             → ~αF G e e′
--             → fvF {G} {F} S e ≡ fvF {G} {F} S e′
-- lemma~fv S ~αV               = refl
-- lemma~fv S ~α1               = refl
-- lemma~fv S ~αE               = refl
-- lemma~fv S (~αEf e~e')       = lemma~fv S e~e'
-- lemma~fv S (~αR e~e')        = lemma~fv S e~e'
-- lemma~fv S (~αinj₁ e~e')     = lemma~fv S e~e'
-- lemma~fv S (~αinj₂ e~e')     = lemma~fv S e~e'
-- lemma~fv S (~αx e~e' e~e'')  = cong₂ _++_ (lemma~fv S e~e') (lemma~fv S e~e'')
-- lemma~fv {F} {|B| S' G} {x , e} {y , e'}
--          S (~αb≡S xs f)
--   with S' ≟S  S
-- ... | no  S'≢S
--   with χ' xs | lemmaχaux∉ xs
-- ... | z      | z∉xs
--   = subst₂ _≡_ (lemmafvSwap {F} {G} S'≢S) (lemmafvSwap {F} {G} S'≢S) (lemma~fv S (f z z∉xs))
-- lemma~fv {G = |B| .S G} {x , e} {y , e'}
--          S (~αb≡S xs f)
--     | yes refl
--   = {!!}
\end{code}
%<*freevariablesneq>
\begin{code}
fvSF≢ : {F G : Functor} → List Sort → ⟦ G ⟧ (μ F) → List V
fvSF≢ {F} {|v| S}      Ss e with any (_≟S_ S) Ss
... | yes _                        =  []
... | no  _                        =  [ e ]
fvSF≢ {F} {|1|}        Ss tt       =  []
fvSF≢ {F} {|E| x}      Ss e        =  []
fvSF≢ {F} {|Ef|   G}   Ss ⟨ e ⟩    =  fvSF≢ {G} {G}  Ss e
fvSF≢ {F} {|R|}        Ss ⟨ e ⟩    =  fvSF≢ {F} {F}  Ss e
fvSF≢ {F} {G₁ |+| G₂}  Ss (inj₁ x) =  fvSF≢ {F} {G₁} Ss x
fvSF≢ {F} {G₁ |+| G₂}  Ss (inj₂ y) =  fvSF≢ {F} {G₂} Ss y
fvSF≢ {F} {G₁ |x| G₂}  Ss (x , y)  =  fvSF≢ {F} {G₁} Ss x ++
                                      fvSF≢ {F} {G₂} Ss y
fvSF≢ {F} {|B| S G}    Ss (x , e) with any (_≟S_ S) Ss
... | yes _                        =  fvSF≢ {F} {G} Ss e 
... | no  _                        =  fvSF≢ {F} {G} (S ∷ Ss) e ++
                                      (fvSF {F} {G} S e - x) 

fvF : {F G : Functor} → ⟦ G ⟧ (μ F) → List V
fvF {F} {G} e = fvSF≢ {F} {G} [] e

fv : {F : Functor} → μ F → List V
fv {F} e = fvF {F} {|R|} e
\end{code}
%</freevariablesneq>

\begin{code}
lemmafvSF≢ :  {F G : Functor}{e : ⟦ G ⟧ (μ F)}{Ss : List Sort}{x : V}{S : Sort}
              → S ∉ Ss → x ∉ fvSF≢ {F} {G} Ss e → freshF S x G e
lemmafvSF≢ {G = |1|}                        S∉Ss x∉ = fresh1
lemmafvSF≢ {G = |R|}        {⟨ e ⟩}         S∉Ss x∉ = freshR     (lemmafvSF≢ S∉Ss x∉)
lemmafvSF≢ {G = |E| x}                      S∉Ss x∉ = freshE
lemmafvSF≢ {G = |Ef| G}     {⟨ e ⟩}         S∉Ss x∉ = freshEf    (lemmafvSF≢ S∉Ss x∉)
lemmafvSF≢ {G = G₁ |+| G₂}  {inj₁ e}        S∉Ss x∉ = freshinj₁  (lemmafvSF≢ S∉Ss x∉)
lemmafvSF≢ {G = G₁ |+| G₂}  {inj₂ e}        S∉Ss x∉ = freshinj₂  (lemmafvSF≢ S∉Ss x∉)
lemmafvSF≢ {F} {G₁ |x| G₂}  {e₁ , e₂} {Ss}  S∉Ss x∉ = freshx     (lemmafvSF≢ S∉Ss (c∉xs++ys→c∉xs x∉))  
                                                                 (lemmafvSF≢ S∉Ss ((c∉xs++ys→c∉ys {xs = fvSF≢ {F} {G₁} Ss e₁} x∉))) 
lemmafvSF≢ {G = |v| S'}     {y}       {Ss}  {x} {S} 
                                            S∉Ss x∉ with any (_≟S_ S') Ss
... | yes  S'∈Ss                                    = freshV≢S   (x∉xs∧y∈xs⇒y≢x S∉Ss S'∈Ss)
... | no   S'∉Ss                                    = freshV≢    (lemmay∈[x]y≢x x∉)
lemmafvSF≢ {G = |B| S' G}   {y , e}   {Ss}  {x} {S}
                                            S∉Ss x∉ with any (_≟S_ S') Ss
... | yes  S'∈Ss                                    = freshb (lemmafvSF≢ S∉Ss x∉) 
... | no   S'∉Ss with S ≟S S' 
...        | no  S≢S'                               = freshb (lemmafvSF≢ (x≢y∧x∉xs⇒x∉y∷xs S≢S' S∉Ss) (c∉xs++ys→c∉xs x∉))
...        | yes _    with y ≟v x
lemmafvSF≢ {G = |B| S G}   {.x , e}   {Ss}  {x} {.S}
                                            S∉Ss x∉
    | no   S'∉Ss | yes refl | yes refl              = freshb≡
lemmafvSF≢ {G = |B| S G}   {y , e}   {Ss}  {x}  {.S}
                                            S∉Ss x∉
    | no   S'∉Ss | yes refl | no y≢x                = freshb (lemmafvSF# ((lemma-∉ {y = y} y≢x (c∉xs++ys→c∉ys {xs = fvSF≢ {G = G} (S ∷ Ss) e} x∉))))

lemmafvF# :  {F G : Functor}{x : V}{S : Sort}{e : ⟦ G ⟧ (μ F)} 
             → x ∉ fvF {F} {G} e → freshF S x G e
lemmafvF# = lemmafvSF≢ (λ ()) 

lemmafv# :  {F : Functor}{x : V}{S : Sort}{e : μ F} 
            → x ∉ fv e → fresh S x e
lemmafv# = lemmafvF#

-- lemmafvtuple :  {F  : Functor}{e₁ e₂ : μ F}
--             → fv {|R| |x| |R|} ⟨ e₁ , e₂ ⟩ ≡ fv e₁ ++ fv e₂
-- lemmafvtuple{e₁ = ⟨ e₁ ⟩} {⟨ e₂ ⟩} = refl

lemmafvtern :  {G₁ G₂ G₃ : Functor}{e₁ : μ G₁}{e₂ : μ G₂}{e₃ : μ G₃}
            → fv {|Ef| G₁ |x| |Ef| G₂ |x| |Ef| G₃ } ⟨ e₁ , e₂ , e₃ ⟩ ≡ fv e₁ ++ fv e₂ ++ fv e₃
lemmafvtern {e₁ = ⟨ e₁ ⟩} {⟨ e₂ ⟩} {⟨ e₃ ⟩} = refl

lemma∉fvfvS : {F : Functor}{S : Sort}{e : μ F}{x : V} → x ∉ fv e → x ∉ fvS S e
lemma∉fvfvS {F} {S} {e} {x} = lemmaS#fvF ∘ (lemmafv# {F} {x} {S} {e})

lemma∈fvSfv : {F : Functor}{S : Sort}{e : μ F}{x : V} → x ∈ fvS S e → x ∈ fv e
lemma∈fvSfv {F} {S} {e} {x} x∈fvSe with any (_≟v_ x) (fv e)
... | yes x∈fve = x∈fve
... | no  x∉fve = ⊥-elim ((lemma∉fvfvS {F} {S} {e} {x} x∉fve) x∈fvSe)

fvSF≢⊆ :  {F G : Functor}{e : ⟦ G ⟧ (μ F)}{xs ys : List Sort}
          → ys ⊆ xs 
          → fvSF≢ {F} {G} xs e ⊆ fvSF≢ {F} {G} ys e
fvSF≢⊆ {F} {|1|}       {e}        {xs} {ys} ys⊆xs = id
fvSF≢⊆ {F} {|R|}       {⟨ e ⟩}    {xs} {ys} ys⊆xs = fvSF≢⊆ {F} {F} {e} ys⊆xs
fvSF≢⊆ {F} {|E| x}     {e}        {xs} {ys} ys⊆xs = id
fvSF≢⊆ {F} {|Ef| G}    {⟨ e ⟩}    {xs} {ys} ys⊆xs = fvSF≢⊆ {G} {G} {e} ys⊆xs
fvSF≢⊆ {F} {G |+| G₁}  {inj₁ e}   {xs} {ys} ys⊆xs = fvSF≢⊆ {F} {G} {e} ys⊆xs
fvSF≢⊆ {F} {G |+| G₁}  {inj₂ e}   {xs} {ys} ys⊆xs = fvSF≢⊆ {F} {G₁} {e} ys⊆xs
fvSF≢⊆ {F} {G₁ |x| G₂} {e₁ , e₂}  {xs} {ys} ys⊆xs = lemma-++ (fvSF≢⊆ {F} {G₁} {e₁} ys⊆xs) (fvSF≢⊆ {F} {G₂} {e₂} ys⊆xs)
fvSF≢⊆ {F} {|v| S} {e}            {xs} {ys} ys⊆xs with any (_≟S_ S) xs
... | yes S∈xs = λ ()
... | no  S∉xs with any (_≟S_ S) ys
...            | yes S∈ys = ⊥-elim (S∉xs (ys⊆xs S∈ys))
...            | no  S∉ys = id
fvSF≢⊆ {F} {|B| S G}    {x , e}   {xs} {ys} ys⊆xs with any (_≟S_ S) xs
... | yes S∈xs with any (_≟S_ S) ys
...             | yes S∈ys = fvSF≢⊆ {F} {G} {e} {xs} {ys} ys⊆xs
...             | no  S∉ys = lemma-++-1 {fvSF≢ {F} {G} xs e} {fvSF≢ {F} {G} (S ∷ ys) e} {fvSF {F} {G} S e - x} (fvSF≢⊆ {F} {G} {e} {xs} {S ∷ ys} (lemma-++-∷-1 S∈xs ys⊆xs))
fvSF≢⊆ {F} {|B| S G}    {x , e}   {xs} {ys} ys⊆xs 
    | no  S∉xs with any (_≟S_ S) ys
...             | yes S∈ys = ⊥-elim (S∉xs (ys⊆xs S∈ys))
...             | no  S∉ys = lemma-++  {fvSF≢ {F} {G} (S ∷ xs) e} {fvSF≢ {F} {G} (S ∷ ys) e} {fvSF {F} {G} S e - x} {fvSF {F} {G} S e - x}
                                       (fvSF≢⊆ {F} {G} {e} {S ∷ xs} {S ∷ ys} (lemma-++-∷-2 ys⊆xs)) id
\end{code}

\begin{code}
foldSFF :  {C H F G : Functor}{S : Sort}{c : μ C}{e : ⟦ G ⟧ (μ F)}{f : ⟦ F ⟧ (μ H) → μ H}
         → ({e  : ⟦ F ⟧ (μ H)}{S : Sort} → fvSF {H} {|R|} S (f e) ⊆ fv c ++ fvSF {H} {F} S e)
         → fvSF {H} {G} S (foldmap F G f e) ⊆ fv c ++ fvSF {F} {G} S e
foldSFF {C} {H} {F} {|1|}      {S} {c} {e}         {f} prf = λ ()
foldSFF {C} {H} {F} {|R|}      {S} {c} {⟨ e ⟩}     {f} prf =
 lemma⊆  {fvSF {H} {|R|} S (f (foldmap F F f e))} {fv c} {fvSF {H} {F} S (foldmap F F f e)} {fvSF {F} {F} S e}
         (prf {S = S})
         (foldSFF {C} {H} {F} {F} {S} {c} {e} {f} prf) 
foldSFF {C} {H} {F} {|E| x}    {S} {c} {e}         {f} prf = λ ()
foldSFF {C} {H} {F} {|Ef| G}   {S} {c} {⟨ e ⟩}     {f} prf = c∈ys→c∈xs++ys {xs = fv c} {fvSF {G} {G} S e}  
foldSFF {C} {H} {F} {G₁ |+| G₂} {S} {c} {inj₁ e}   {f} prf = foldSFF {C} {H} {F} {G₁} {S} {c} {e} {f} prf
foldSFF {C} {H} {F} {G₁ |+| G₂} {S} {c} {inj₂ e}   {f} prf = foldSFF {C} {H} {F} {G₂} {S} {c} {e} {f} prf
foldSFF {C} {H} {F} {G₁ |x| G₂} {S} {c} {e₁ , e₂}  {f} prf 
  = lemma⊆m  {fvSF {H} {G₁} S (foldmap F G₁ f e₁)} 
             {fvSF {H} {G₂} S (foldmap F G₂ f e₂)} 
             {fvSF {F} {G₁} S e₁} {fvSF {F} {G₂} S e₂}
             {fv c}
             (foldSFF {C} {H} {F} {G₁} {S} {c} {e₁} {f} prf)
             (foldSFF {C} {H} {F} {G₂} {S} {c} {e₂} {f} prf)
foldSFF {C} {H} {F} {|v| S′}    {S} {c} {x}          {f} prf with S′ ≟S  S
... | yes _  = c∈ys→c∈xs++ys {xs = fv c} 
... | no  _  = λ ()
foldSFF {C} {H} {F} {|B| S′ G}  {S} {c} {x , e}      {f} prf with S′ ≟S  S
... | yes _ = lemma-⊆ {x} {fvSF {H} {G} S (foldmap F G f e)} {fvSF {F} {G} S e} {fv c}
                      (foldSFF {C} {H} {F} {G} {S} {c} {e} {f} prf)
... | no  _ = foldSFF {C} {H} {F} {G} {S} {c} {e} {f} prf 

foldSF :  {C H F : Functor}{S : Sort}{c : μ C}{e : μ F}{f : ⟦ F ⟧ (μ H) → μ H}
         → ({e  : ⟦ F ⟧ (μ H)}{S : Sort} → fvSF {H} {|R|} S (f e) ⊆ fv c ++ fvSF {H} {F} S e)
         → fvS S (fold F f e) ⊆ fv c ++ fvS S e
foldSF {C} {H} {F} {S} {c} {e} = foldSFF {C} {H} {F} {|R|} {S} {c} {e} 

foldFVF :  {C H F G : Functor}{c : μ C}{e : ⟦ G ⟧ (μ F)}{f : ⟦ F ⟧ (μ H) → μ H}{xs : List Sort}
--         → ({e  : ⟦ F ⟧ (μ H)}{ys : List Sort} → fvSF≢ {H} {|R|} ys (f e) ⊆ fvSF≢ {C} {|R|} ys c ++ fvSF≢ {H} {F} ys e)
         → ({e  : ⟦ F ⟧ (μ H)}{ys : List Sort} → fvSF≢ {H} {|R|} ys (f e) ⊆ fv c ++ fvSF≢ {H} {F} ys e)
         → ({e  : ⟦ F ⟧ (μ H)}{S : Sort} → fvSF {H} {|R|} S (f e) ⊆ fv c ++ fvSF {H} {F} S e)                      
         → fvSF≢ {H} {G} xs (foldmap F G f e) ⊆ fv c ++ fvSF≢ {F} {G} xs e
foldFVF {C} {H} {F} {|1|}      {c} {e}         {f} {xs} prf prf2 = λ ()
foldFVF {C} {H} {F} {|R|}      {c} {⟨ e ⟩}     {f} {xs} prf prf2
  = lemma⊆ {fvSF≢ {H} {|R|} xs (f (foldmap F F f e))} {fv c} {fvSF≢ {H} {F} xs (foldmap F F f e)} {fvSF≢ {F} {F} xs e}
      (prf {ys = xs})
      (foldFVF {C} {H} {F} {F} {c} {e} {f} {xs} prf prf2)
foldFVF {C} {H} {F} {|E| x}    {c} {e}         {f} {xs} prf prf2 = λ ()
foldFVF {C} {H} {F} {|Ef| G}   {c} {⟨ e ⟩}     {f} {xs} prf prf2 = c∈ys→c∈xs++ys {xs = fv c} {fvSF≢ {G} {G} xs e}  
foldFVF {C} {H} {F} {G₁ |+| G₂} {c} {inj₁ e}   {f} {xs} prf prf2 = foldFVF {C} {H} {F} {G₁} {c} {e} {f} {xs} prf prf2
foldFVF {C} {H} {F} {G₁ |+| G₂} {c} {inj₂ e}   {f} {xs} prf prf2 = foldFVF {C} {H} {F} {G₂} {c} {e} {f} {xs} prf prf2
foldFVF {C} {H} {F} {G₁ |x| G₂} {c} {e₁ , e₂}  {f} {xs} prf prf2 
  = lemma⊆m  {fvSF≢ {H} {G₁} xs (foldmap F G₁ f e₁)} 
             {fvSF≢ {H} {G₂} xs (foldmap F G₂ f e₂)} 
             {fvSF≢ {F} {G₁} xs e₁} {fvSF≢ {F} {G₂} xs e₂}
             {fv c}
             (foldFVF {C} {H} {F} {G₁} {c} {e₁} {f} {xs} prf prf2)
             (foldFVF {C} {H} {F} {G₂} {c} {e₂} {f} {xs} prf prf2)
foldFVF {C} {H} {F} {|v| S}    {c} {e}          {f} {xs} prf prf2 with any (_≟S_ S) xs
... | yes _ = λ ()
... | no  _ = c∈ys→c∈xs++ys {xs = fv c} 
foldFVF {C} {H} {F} {|B| S G}  {c} {x , e}      {f} {xs} prf prf2 with any (_≟S_ S) xs
... | yes _ = foldFVF {C} {H} {F} {G} {c} {e} {f} {xs} prf prf2 
... | no  _ = lemma⊆m  {fvSF≢ {H} {G} (S ∷ xs) (foldmap F G f e)} {fvSF {H} {G} S (foldmap F G f e) - x}
                       {fvSF≢ {F} {G} (S ∷ xs) e} {fvSF {F} {G} S e - x} {fv c}
                       (foldFVF {C} {H} {F} {G} {c} {e} {f} {S ∷ xs} prf prf2)
                       (lemma-⊆ {x} {fvSF {H} {G} S (foldmap F G f e)} {fvSF {F} {G} S e} {fv c} (foldSFF {C} {H} {F} {G} {S} {c} {e} {f} prf2))

foldFV :  {C H F : Functor}{c : μ C}{e : μ F}{f : ⟦ F ⟧ (μ H) → μ H}
--         → ({e  : ⟦ F ⟧ (μ H)}{ys : List Sort} → fvSF≢ {H} {|R|} ys (f e) ⊆ fvSF≢ {C} {|R|} ys c ++ fvSF≢ {H} {F} ys e)
         → ({e  : ⟦ F ⟧ (μ H)}{ys : List Sort} → fvSF≢ {H} {|R|} ys (f e) ⊆ fv c ++ fvSF≢ {H} {F} ys e)
         → ({e  : ⟦ F ⟧ (μ H)}{S : Sort} → fvSF {H} {|R|} S (f e) ⊆ fv c ++ fvSF {H} {F} S e)                      
         → fv (fold F f e) ⊆ fv c ++ fv e
foldFV {C} {H} {F} {c} {e} = foldFVF {C} {H} {F} {|R|} {c} {e} {xs = []}

foldCtxFV :  {C H F : Functor}{c : μ C}{e : μ F}
             {f : μ C → ⟦ F ⟧ (μ H) → μ H}
             → ({e  : ⟦ F ⟧ (μ H)}{ys : List Sort} → fvSF≢ {H} {|R|} ys (f c e) ⊆ fv c ++ fvSF≢ {H} {F} ys e)
--             → ({e  : ⟦ F ⟧ (μ H)}{ys : List Sort} → fvSF≢ {H} {|R|} ys (f c e) ⊆ fvSF≢ {C} {|R|} ys c ++ fvSF≢ {H} {F} ys e)
             → ({e  : ⟦ F ⟧ (μ H)}{S : Sort} → fvSF {H} {|R|} S (f c e) ⊆ fv c ++ fvSF {H} {F} S e)             
             → fv (foldCtx F f c e) ⊆ fv c ++ fv e
foldCtxFV {C} {H} {F} {c} {e} = foldFV {C} {H} {F} {c} {e}
\end{code}


