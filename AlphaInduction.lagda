\begin{code}
module AlphaInduction where

open import GPBindings
open import Alpha
open import OccurBind
open import FreeVariables
open import Swap
open import Fresh
open import List.ListProperties
open import List.NotInList
open import Chi

open import Function
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.List
open import Data.List.All
open import Relation.Nullary
open import Data.Product hiding (swap)
open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]ᵢ)

bindersFreeαElemF : 
    {F : Functor}(G : Functor)(xs : List V)(e : ⟦ G ⟧ (μ F))
    → AccF F G e
    → ∃ (λ e' → ListNotOccurBindF {F} G xs e')
bindersFreeαElemF (|v| x)        xs e     _
  = e , lemma-bindsv
bindersFreeαElemF |1|            xs e     _
  = e , lemma-binds1
bindersFreeαElemF (|E| x)        xs e     _
  = e , lemma-bindsE
bindersFreeαElemF (|Ef| G)       xs ⟨ e ⟩ (accEf acce)
  = Data.Product.map  (⟨_⟩) 
                      lemma-bindsEf
                      (bindersFreeαElemF G xs e acce)
bindersFreeαElemF {F} |R|        xs ⟨ e ⟩ (accR acce)      
  = Data.Product.map  (⟨_⟩) 
                      lemma-bindsR
                      (bindersFreeαElemF F xs e acce)
bindersFreeαElemF (G₁ |+| G₂)    xs (inj₁ e) (acc+₁ acce)  
  = Data.Product.map  inj₁ 
                      lemma-binds+1 
                      (bindersFreeαElemF G₁ xs e acce)
bindersFreeαElemF (G₁ |+| G₂)    xs (inj₂ e) (acc+₂ acce)  
  = Data.Product.map  inj₂
                      lemma-binds+2 
                      (bindersFreeαElemF G₂ xs e acce)
bindersFreeαElemF (G₁ |x| G₂)    xs (e₁ , e₂) (accx acce₁ acce₂)
  with  bindersFreeαElemF G₁ xs e₁ acce₁ | bindersFreeαElemF G₂ xs e₂ acce₂
... | (e₁′ , notOccur₁) | (e₂′ , notOccur₂)
  = (e₁′ , e₂′) , lemma-binds× notOccur₁ notOccur₂
bindersFreeαElemF {F} (|B| S G)  xs (x , e) (accB facc)
  with fvF {F} {|B| S G} (x , e)      
... | zs
  with χ' (xs ++ zs) | lemmaχaux∉ (xs ++ zs)
... | z  | z∉xs++fv
  = Data.Product.map  (λ e' → (z , e'))
                      (lemma-bindsB (c∉xs++ys→c∉xs z∉xs++fv))
                      (bindersFreeαElemF G xs (swapF G S x z e) (facc z))
\end{code}

%<*bindersfreealphaelem>
\begin{code}
bindersFreeαElem : {F : Functor}(xs : List V)(e : μ F) → ∃ (λ e' → ListNotOccurBind {F} xs e')
\end{code}
%</bindersfreealphaelem>

\begin{code}
bindersFreeαElem {F} xs e = bindersFreeαElemF {F} |R| xs e (accF e)

lemma-bindersFreeαElemF : {F : Functor}(G : Functor)(xs : List V)(e e' : ⟦ G ⟧ (μ F))
    → ∼αF G e e' 
    → (acce : AccF F G e) → (acce' : AccF F G e')
    → bindersFreeαElemF G xs e acce ≡ bindersFreeαElemF G xs e' acce'
lemma-bindersFreeαElemF (|v| x)     xs e      .e      ∼αV          _ _ = refl
lemma-bindersFreeαElemF |1|         xs .tt    .tt     ∼α1          _ _ = refl
lemma-bindersFreeαElemF (|E| x)     xs e      .e      ∼αE          _ _ = refl
lemma-bindersFreeαElemF (|Ef| G)    xs ⟨ e ⟩   ⟨ e' ⟩      (∼αEf e∼e')  (accEf acce) (accEf acce')
  = cong  (Data.Product.map  (⟨_⟩) lemma-bindsEf)
          (lemma-bindersFreeαElemF G xs e e' e∼e' acce acce')
lemma-bindersFreeαElemF {F} |R|     xs ⟨ e ⟩  ⟨ e' ⟩  (∼αR e∼e') (accR acce) (accR acce')
  = cong  (Data.Product.map  (⟨_⟩) lemma-bindsR)
          (lemma-bindersFreeαElemF F xs e e' e∼e' acce acce')  
lemma-bindersFreeαElemF (G₁ |+| G₂)  xs (inj₁ e) (inj₁ e') (∼α+₁ e∼e') (acc+₁ acce) (acc+₁ acce')
  = cong  (Data.Product.map  inj₁ lemma-binds+1)
          (lemma-bindersFreeαElemF G₁ xs e e' e∼e' acce acce')   
lemma-bindersFreeαElemF (G₁ |+| G₂)  xs (inj₂ e) (inj₂ e') (∼α+₂ e∼e') (acc+₂ acce) (acc+₂ acce')
  = cong  (Data.Product.map  inj₂ lemma-binds+2)
          (lemma-bindersFreeαElemF G₂ xs e e' e∼e' acce acce')   
lemma-bindersFreeαElemF (G₁ |x| G₂)  xs (e₁ , e₂) (e₁′ , e₂′) (∼αx e₁∼e₁′ e₂∼e₂′) (accx acce₁ acce₂) (accx acce₁′ acce₂′)
  with bindersFreeαElemF G₁ xs e₁ acce₁ | bindersFreeαElemF G₂ xs e₂ acce₂ |
       bindersFreeαElemF G₁ xs e₁′ acce₁′ | bindersFreeαElemF G₂ xs e₂′ acce₂′ |
       lemma-bindersFreeαElemF G₁ xs e₁ e₁′ e₁∼e₁′ acce₁ acce₁′ | lemma-bindersFreeαElemF G₂ xs e₂ e₂′ e₂∼e₂′ acce₂ acce₂′
... | (e₁″ , notOccur₁) | (e₂″ , notOccur₂) | .(e₁″ , notOccur₁) | .(e₂″ , notOccur₂) | refl | refl
  = refl
lemma-bindersFreeαElemF {F} (|B| S G) xs (x , e) (y , e′) xe∼ye′ (accB facce) (accB facce′)
  with  fvF {F} {|B| S G} (x , e)
  |     inspect (fvF {F} {|B| S G}) (x , e)
  |     fvF {F} {|B| S G} (y , e′)
  |     lemma∼fvF [] xe∼ye′
... | zs | [ fv≡zs ]ᵢ | .zs | refl 
  with  χ' (xs ++ zs)  | lemmaχaux∉ (xs ++ zs)
... | z | z∉xs++fv
  = cong  (Data.Product.map  (λ e' → (z , e')) 
                             (lemma-bindsB (c∉xs++ys→c∉xs z∉xs++fv)))
          (lemma-bindersFreeαElemF {F} G xs (swapF G S x z e) (swapF G S y z e′) (lemma∼B xe∼ye′ z#xe) (facce z) (facce′ z))
  where
  z∉fv : z ∉ fvF {F} {|B| S G} (x , e) 
  z∉fv = subst (_∉_ z)  (sym fv≡zs) (c∉xs++ys→c∉ys {z} {xs} z∉xs++fv)
  z#xe : freshF S z (|B| S G) (x , e)
  z#xe = lemmafvF# z∉fv
\end{code}

%<*bindersalpha>
\begin{code}
lemma-bindersFreeαElem : 
    {F : Functor}(xs : List V)(e e' : μ F) 
    → e ∼α e' 
    → bindersFreeαElem xs e ≡ bindersFreeαElem xs e'
\end{code}
%</bindersalpha>

\begin{code}
lemma-bindersFreeαElem {F} xs e e' e∼e'
  = lemma-bindersFreeαElemF |R| xs e e' e∼e' (accF e) (accF e')

lemma-bindersFreeαAlphaF : 
    {F : Functor}(G : Functor)(xs : List V)(e  : ⟦ G ⟧ (μ F)) 
    → (acce : AccF F G e)
    → ∼αF G (proj₁ (bindersFreeαElemF G xs e acce)) e
lemma-bindersFreeαAlphaF (|v| x)     xs e          _                   = ∼αV
lemma-bindersFreeαAlphaF |1|         xs e          _                   = ∼α1
lemma-bindersFreeαAlphaF (|E| B)     xs e          _                   = ∼αE
lemma-bindersFreeαAlphaF (|Ef| G)    xs ⟨ e ⟩      (accEf acce)        = ∼αEf    (lemma-bindersFreeαAlphaF G xs e acce)
lemma-bindersFreeαAlphaF {F} |R|     xs ⟨ e ⟩      (accR  acce)        = ∼αR     (lemma-bindersFreeαAlphaF F xs e acce)
lemma-bindersFreeαAlphaF (G₁ |+| G₂) xs (inj₁ e)   (acc+₁ acce)        = ∼α+₁    (lemma-bindersFreeαAlphaF G₁ xs e acce)
lemma-bindersFreeαAlphaF (G₁ |+| G₂) xs (inj₂ e)   (acc+₂ acce)        = ∼α+₂    (lemma-bindersFreeαAlphaF G₂ xs e acce)
lemma-bindersFreeαAlphaF (G₁ |x| G₂) xs (e₁ , e₂)  (accx acce₁ acce₂)  = ∼αx     (lemma-bindersFreeαAlphaF G₁ xs e₁ acce₁) 
                                                                                 (lemma-bindersFreeαAlphaF G₂ xs e₂ acce₂)
lemma-bindersFreeαAlphaF {F} (|B| S G)   xs (x , e) (accB facc)
  with  fvF {F} {|B| S G}  (x , e)
  |     inspect (fvF {F} {|B| S G}) (x , e)
... | zs | [ fv≡zs ]ᵢ   
  with  χ' (xs ++ zs)  | lemmaχaux∉ (xs ++ zs)
... | z  | z∉xs++fv
  = ∼αB zs (λ y y∉zs → lemma∼ y∉zs)
  where
  open ∼F-Reasoning(F)(G)
  lemma∼ : {y : V} → y ∉ zs 
         → ∼αF G  (swapF G S z y (proj₁ (bindersFreeαElemF G xs (swapF G S x z e) (facc z))))
                  (swapF G S x y e)
  lemma∼ {y} y∉zs
    =  begin
         swapF G S z y (proj₁ (bindersFreeαElemF G xs (swapF G S x z e) (facc z)))
       ∼⟨ lemma∼swapEquivF (lemma-bindersFreeαAlphaF G xs (swapF G S x z e) (facc z)) z y ⟩
         swapF G S z y (swapF G S x z e)
       ∼⟨ lemma∼swapCancelFƛ z#xe y#xe ⟩
         swapF G S x y e
       ∎
    where
    z∉fv : z ∉ fvF  {F} {|B| S G} (x , e) 
    z∉fv = subst (_∉_ z)  (sym fv≡zs) (c∉xs++ys→c∉ys {z} {xs} z∉xs++fv)
    z#xe : freshF S z (|B| S G) (x , e)
    z#xe = lemmafvF# z∉fv
    y∉fv : y ∉ fvF {F} {|B| S G} (x , e) 
    y∉fv = subst (_∉_ y)  (sym fv≡zs) y∉zs
    y#xe : freshF S y (|B| S G) (x , e)
    y#xe = lemmafvF# y∉fv
\end{code}


\begin{code}
lemma-bindersFreeαFVα : 
    {F : Functor}{e e' : μ F}
    → e ∼α e' 
    → proj₁ (bindersFreeαElem (fv e) e) ≡ proj₁ (bindersFreeαElem (fv e') e')
lemma-bindersFreeαFVα {e = e} {e'} e∼e' with fv e | fv e' | lemma∼fv e∼e' 
... | fve | .fve | refl
  with bindersFreeαElem fve e | bindersFreeαElem fve e' | lemma-bindersFreeαElem fve e e' e∼e'
... | (r , pr)   | (.r , .pr)  | refl = refl
\end{code}


%<*lemmabindersfreealpha>
\begin{code}
lemma-bindersFreeαAlpha : 
    {F : Functor}(xs : List V)(e  : μ F) 
    → proj₁ (bindersFreeαElem xs e) ∼α e
\end{code}
%</lemmabindersfreealpha>

\begin{code}
lemma-bindersFreeαAlpha {F} xs e = (lemma-bindersFreeαAlphaF |R| xs e (accF e))
\end{code}

\begin{code}
bindersFreeα : {F : Functor}(xs : List V)(e : μ F) → μ F
bindersFreeα xs e = proj₁ (bindersFreeαElem (fv e ++ xs) e)

lemma-bindersFreeα-α : {F : Functor}(xs : List V)(e : μ F)
  → bindersFreeα xs e ∼α e
lemma-bindersFreeα-α xs e = lemma-bindersFreeαAlpha (fv e ++ xs) e

lemma-bindersFreeα-αCompatible : 
    {F : Functor}{xs : List V}{e e' : μ F}
    → e ∼α e' → bindersFreeα xs e ≡ bindersFreeα xs e'
lemma-bindersFreeα-αCompatible {F} {xs} {e} {e'} e∼e' with fv e | fv e' | lemma∼fv e∼e' 
... | fve | .fve | refl
  with bindersFreeαElem (fve ++ xs) e | bindersFreeαElem (fve ++ xs) e' | lemma-bindersFreeαElem (fve ++ xs) e e' e∼e'
... | (r , pr)   | (.r , .pr)  | refl = refl

lemma-bindersFreeα-∉b : {F : Functor}(xs : List V)(e : μ F)
  → ListNotOccurBind {F} ((fv (bindersFreeα xs e)) ++ xs) (bindersFreeα xs e)
lemma-bindersFreeα-∉b xs e
  = subst  (λ ys → ListNotOccurBind (ys ++ xs) (bindersFreeα xs e))
           (sym (lemma∼fv (lemma-bindersFreeαAlpha (fv e ++ xs) e)))
           (proj₂ (bindersFreeαElem (fv e ++ xs) e))

lemma-bindersFreeα-FV∉b : {F : Functor}(xs : List V)(e : μ F)
  → ListNotOccurBind {F} (fv (bindersFreeα xs e)) (bindersFreeα xs e)
lemma-bindersFreeα-FV∉b xs e = lemma-binds++l (lemma-bindersFreeα-∉b xs e)
\end{code}

\begin{code}
αCompatiblePred : {F : Functor} → (μ F → Set) → Set
αCompatiblePred {F = F} P = {e e' : μ F} → e ∼α e' → P e → P e'
\end{code}

%<*strongalphacompatible>
\begin{code}
strong∼αCompatible  : {A : Set}{F : Functor} 
                    → (μ F → A) → μ F → Set
strong∼αCompatible f M = ∀ N → M ∼α N → f M ≡ f N
\end{code}
%</strongalphacompatible>

%<*alphainductionhypotheses>
\begin{code}
fihα :  {F : Functor}(G : Functor)(P : μ F → Set) → List V →  ⟦ G ⟧ (μ F) → Set
\end{code}
%</alphainductionhypotheses>

%<*alphainductionhypothesescases>
\begin{code}
fihα |R|           P xs e          =  P e      × (∀ a → a ∈ xs → a notOccurBind e)
fihα (|B| S   G)   P xs (x , e)    =  x ∉ xs   × fihα G  P xs e
\end{code}
%</alphainductionhypothesescases>

\begin{code}
fihα (|v|   S)     P xs n          =  ⊤
fihα |1|           P xs tt         =  ⊤
fihα (|E|   B)     P xs b          =  ⊤
fihα (|Ef|  G)     P xs e          =  ⊤
fihα (G₁ |+|  G₂)  P xs (inj₁ e)   =  fihα G₁  P xs e 
fihα (G₁ |+|  G₂)  P xs (inj₂ e)   =  fihα G₂  P xs e 
fihα (G₁ |x|  G₂)  P xs (e₁ , e₂)  =  fihα G₁  P xs e₁  × fihα G₂ P xs e₂
\end{code}


\begin{code}
lemma-fih∧notOccurBind⇛fihα : 
     {F : Functor}(G : Functor)(P : μ F → Set)(e : ⟦ G ⟧ (μ F))(xs : List V) 
     → fih {F} G (λ e' → (∀ c → c ∈ xs → c notOccurBind e') → P e') e 
     → (∀ c → c ∈ xs → notOccurBindF c {F} G e)
     → fihα {F} G                       P xs e
lemma-fih∧notOccurBind⇛fihα (|v| x)     P e          xs fih notOccur   = tt
lemma-fih∧notOccurBind⇛fihα |1|         P e          xs fih notOccur   = tt
lemma-fih∧notOccurBind⇛fihα (|E| x)     P e          xs fih notOccur   = tt
lemma-fih∧notOccurBind⇛fihα (|Ef| G)    P e          xs fih notOccur   = tt
lemma-fih∧notOccurBind⇛fihα |R|         P e          xs fih notOccurR  = fih notOccurR , notOccurR
lemma-fih∧notOccurBind⇛fihα (G₁ |+| G₂) P (inj₁ e)   xs fih notOccurinj₁   
  = lemma-fih∧notOccurBind⇛fihα G₁    P e xs fih (λ c c∈xs → notOccurBinj₁inv (notOccurinj₁ c c∈xs))
lemma-fih∧notOccurBind⇛fihα (G₁ |+| G₂) P (inj₂ e)   xs fih notOccurinj₂   
  = lemma-fih∧notOccurBind⇛fihα G₂    P e xs fih (λ c c∈xs → notOccurBinj₂inv (notOccurinj₂ c c∈xs))
lemma-fih∧notOccurBind⇛fihα (G₁ |x| G₂) P (e₁ , e₂)  xs (fih₁ , fih₂) notOccur   
  = lemma-fih∧notOccurBind⇛fihα G₁  P e₁ xs fih₁ (λ c c∈xs → notOccurBx₁inv (notOccur c c∈xs)) ,
    lemma-fih∧notOccurBind⇛fihα G₂  P e₂ xs fih₂ (λ c c∈xs → notOccurBx₂inv (notOccur c c∈xs))
lemma-fih∧notOccurBind⇛fihα (|B| S G)   P (a  , e)   xs fih notOccur   
  with Any.any (_≟v_ a) xs
... | yes a∈xs 
  = ⊥-elim ((notOccurBBinv≢ (notOccur a a∈xs)) refl) 
... | no a∉xs  
  = a∉xs , lemma-fih∧notOccurBind⇛fihα G P e xs fih (λ c c∈xs → notOccurBBinv (notOccur c c∈xs))

-- aux : {F : Functor}(P : μ F → Set)(xs : List V)
--       → ((e : ⟦ F ⟧ (μ F)) → fihα F P xs e → P ⟨ e ⟩)      
--       → (e : ⟦ F ⟧ (μ F)) 
--       → fih F (λ e' → (∀ c → c ∈ xs → c notOccurBind e') → P e') e
--       → ((c : V) → c ∈ xs → _notOccurBind_ {F} c ⟨ e ⟩) 
--       → P ⟨ e ⟩
-- aux {F} P xs hiα e hi notBind
--   = hiα e (lemma-fih∧notOccurBind⇛fihα {F} F P e xs hi (λ c c∈xs → notOccurBRinv (notBind c c∈xs)))
\end{code}

%<*alphainductionprinciple>
\begin{code}
αPrimInd : {F : Functor}(P : μ F → Set)(xs : List V) → αCompatiblePred P 
  → ((e : ⟦ F ⟧ (μ F)) → fihα F P xs e → P ⟨ e ⟩) → ∀ e → P e
\end{code}
%</alphainductionprinciple>

\begin{code}
αPrimInd {F} P xs αP p e
  with bindersFreeαElem xs e
     | lemma-bindersFreeαAlpha xs e
...  | e' , notBind | e'∼e
  = αP  e'∼e
        (foldInd  F 
          (λ e → (∀ c → c ∈ xs → c notOccurBind e) → P e)
          (λ e hi notBind
            → (p  e
                  (lemma-fih∧notOccurBind⇛fihα  {F} F P e xs hi
                     (λ c c∈xs → notOccurBRinv (notBind c c∈xs)))))
          e' 
          (get notBind))
\end{code}
-- (aux {F} P xs p)
                         
-- αIteration : {F : Functor}{A : Set}(xs : List V)
--   → ((e : ⟦ F ⟧ (μ F)) → fihα F (const A) e xs → A)
--   → (e : μ F) → A
-- αIteration {A = A} xs f e = αPrimInd (const A) xs (const id) f e

-- lemma-αIteration-StrongαCompatible : 
--   {F : Functor}{A : Set}{xs : List V}{f : (e : ⟦ F ⟧ (μ F)) → fihα F (const A) e xs → A}
--   → {e : μ F} 
--   → strong∼αCompatible (αIteration xs f) e
-- lemma-αIteration-StrongαCompatible {xs = xs} {f} {e} e' e∼αe' 
--   with bindersFreeαElem xs e | bindersFreeαElem xs e' 
--   | lemma-bindersFreeαElem xs e e' e∼αe' 
-- ... | (x , b) | (.x , .b) | refl = refl

{- Another way to obtain α Iteration -}
-- foldα : {A : Set}(F : Functor) → List V → (⟦ F ⟧ A → A) → μ F → A
-- foldα F xs f e with bindersFreeαElem xs e
-- ... | e′ , _ = fold  F f e′
\end{code}





%<*foldCtxalpha>
\begin{code}
foldCtxα :  {C H : Functor}(F : Functor) → (μ C → ⟦ F ⟧ (μ H)  → μ H) → μ C → μ F → μ H
foldCtxα F f c e = foldCtx F f c (proj₁ (bindersFreeαElem (fv c) e))
\end{code}
%</foldCtxalpha>

%<*lemmafoldCtxalpha>
\begin{code}
lemma-foldCtxα-foldCtx : {C H : Functor}(F : Functor){f : μ C → ⟦ F ⟧ (μ H) → μ H}{c : μ C}{e : μ F}
  →  ({e e′  :  ⟦ F ⟧ (μ H)}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
  →  ({c     : μ C}{S : Sort}  {x y : V}{e : ⟦ F ⟧ (μ H)}
             → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
  →  ListNotOccurBind (fv c) e
  →  foldCtxα F f c e ∼α foldCtx F f c e
\end{code}
%</lemmafoldCtxalpha>

\begin{code}
lemma-foldCtxα-foldCtx F {c = c} {e} prf prf2 cNotBinde with bindersFreeαElem (fv c) e | lemma-bindersFreeαAlpha (fv c) e
... | e′ , nb | e′∼e = lemma-foldCtxα prf prf2 nb cNotBinde ρ e′∼e  
\end{code}


%<*foldCtxalphastrongalphacompatible>
\begin{code}
lemma-foldCtxα-StrongαCompatible :
  {C H F : Functor}{f : μ C → ⟦ F ⟧ (μ H)  → μ H}{c : μ C}{e : μ F}
  → strong∼αCompatible (foldCtxα F f c) e
\end{code}
%</foldCtxalphastrongalphacompatible>

\begin{code}
lemma-foldCtxα-StrongαCompatible {f = f} {c} {e} e' e∼αe' 
  with bindersFreeαElem (fv c) e | bindersFreeαElem (fv c) e' 
  | lemma-bindersFreeαElem (fv c) e e' e∼αe' 
... | (x , b) | (.x , .b) | refl = refl
\end{code}

%<*alphaproof>
\begin{code}
αProof : {F : Functor}(P : μ F → Set)(xs : List V)
  → αCompatiblePred P 
  → ((e : μ F)  → ListNotOccurBind xs e → ListNotOccurBind (fv e)  e
                → P e )  
  → ∀ e → P e
\end{code}
%</alphaproof>

\begin{code}
αProof P xs αC proof e
     with  bindersFreeαElem         (xs ++ (fv e)) e
     |     lemma-bindersFreeαAlpha  (xs ++ (fv e)) e
...  | e' , notBind | e'∼e
  = αC e'∼e (proof e' nb1 nb2)
  where
  nb1 : ListNotOccurBind xs e'
  nb1 = lemma-binds++l notBind
  nb2 : ListNotOccurBind (fv e') e'
  nb2 = subst  (λ e → ListNotOccurBind e e')
               (lemma∼fv (σ e'∼e))
               (lemma-binds++r {xs} notBind)
\end{code}

%<*foldctxalpha-cxtalpha>
\begin{code}
lemma-foldCtxα-cxtα  : {F H C : Functor}
     {f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c′ : μ C}
  →  ({e e′ :  ⟦ F ⟧ (μ H)}{c c′ : μ C} 
               → c ∼α c′ → ∼αF F e e′ 
               → f c e ∼α f c′ e′)               
  →  c ∼α c′
  →  (e : μ F) → foldCtxα F f c e ∼α foldCtxα F f c′ e
\end{code}
%</foldctxalpha-cxtalpha>

\begin{code}
lemma-foldCtxα-cxtα {c = c} {c′} prf c∼c′ e 
  with fv c | fv c′ | lemma∼fv c∼c′
... | fv | .fv | refl = lemma-foldCtxαCtx prf c∼c′ (proj₁ (bindersFreeαElem fv e))
\end{code}


--   lemma-binderFreeElemFold :
--     {F H C : Functor}{f : μ C → ⟦ F ⟧ (μ H) → μ H}{c c' : μ C}{e : μ F}{S : Sort}
--     → proj₁ (bindersFreeαElem (fv S c) (foldS F f c' e))  ∼α
--       foldS F f (proj₁ (bindersFreeαElem (fv S c) c')) (proj₁ (bindersFreeαElem (fv S c) e))
-- binder (y,P) (M[x:=N]n) ∼ (binder (y,P) M) [ x := binder (y,P) N ] ????

{- Substitution Example - Can be done generically ? -}
-- substAux : {F : Functor}(G : Functor) 
--   → (x : V) → (e' : μ F) → (S : Sort) 
--   → (e : ⟦ G ⟧ (μ F)) 
--   → fihα G (const (⟦ F ⟧ (μ F))) e (x ∷ fv S e') 
--   →  ⟦ G ⟧ (μ F) ⊎ μ F
-- substAux (|v| S')    x e' S e         fihα    = {!!}
-- substAux |1|         x e' S e         fihα    = inj₁ tt
-- substAux (|E| B)     x e' S e         fihα    = inj₁ e
-- substAux (|Ef| G)    x e' S ⟨ e ⟩     fihα    = {! substAux {G} G x e' S e fihα)!}
-- substAux |R|         x e' S ⟨ e ⟩     (r , _) = inj₁ ⟨ r ⟩
-- substAux (G₁ |+| G₂) x e' S (inj₁ e)  fihα    = [ inj₁ ∘ inj₁ , inj₂ ]′ (substAux G₁ x e' S e fihα)
-- substAux (G₁ |+| G₂) x e' S (inj₂ e)  fihα    = [ inj₁ ∘ inj₂ , inj₂ ]′ (substAux G₂ x e' S e fihα)
-- substAux (G₁ |x| G₂) x e' S (e₁ , e₂) (fihα₁ , fihα₂) = {! !}
-- substAux (|B| S' G)  x e' S (y  , e)  fihα   = {!!}

-- substAux' : (F : Functor) 
--   → (x : V) → (e' : μ F) → (S : Sort) 
--   → (e : ⟦ F ⟧ (μ F)) 
--   → fihα F (const (⟦ F ⟧ (μ F))) e (x ∷ fv S e') 
--   → ⟦ F ⟧ (μ F)
-- substAux' F x e' S e fihα with substAux {F} F x e' S e fihα
-- ... | inj₁ r      = r
-- ... | inj₂ ⟨ r ⟩  = r

-- _[_≔_]_ : {F : Functor} → μ F → V → μ F → Sort → μ F
-- _[_≔_]_ {F} e x e' S = ⟨ αIteration (x ∷ fv S e') (substAux' F x e' S) e ⟩

Recursion

-- \begin{code}
-- recCtxα :  {C H : Functor}(F : Functor)
--             → (μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))  → μ H)
--             → μ C → μ F → μ H
-- recCtxα F f c e = recCtx F f c (proj₁ (bindersFreeαElem (fv c) e))
-- \end{code}

-- \begin{code}
-- lemma-recCtxα-StrongαCompatible :
--   {C H F : Functor}{f : μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H}{c : μ C}{e : μ F}
--   → strong∼αCompatible (recCtxα F f c) e
-- \end{code}

-- \begin{code}
-- lemma-recCtxα-StrongαCompatible {f = f} {c} {e} e' e∼αe' 
--   with bindersFreeαElem (fv c) e | bindersFreeαElem (fv c) e' 
--   | lemma-bindersFreeαElem (fv c) e e' e∼αe' 
-- ... | (x , b) | (.x , .b) | refl = refl
-- \end{code}

-- \begin{code}
-- lemma-recmapSCtx  : {F H C : Functor}(G : Functor)
--               {f : μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H}{c c′ : μ C}
--               → ({e e′ :  ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)  
--               → c ∼α c′
--               → (e : ⟦ G ⟧ (μ F)) → ∼αF G (recmapCtx F G f c e) (recmapCtx F G f c′ e)
-- lemma-recmapSCtx (|v| S)      prf c∼c′  e          = ∼αV
-- lemma-recmapSCtx |1|          prf c∼c′  e          = ∼α1
-- lemma-recmapSCtx {F} |R|      prf c∼c′  ⟨ e ⟩      = ∼αR (∼αx (lemma-∼αR (prf c∼c′   (lemma-recmapSCtx F prf c∼c′ e))) ρF)    
-- lemma-recmapSCtx (|E| x)      prf c∼c′  e          = ∼αE 
-- lemma-recmapSCtx (|Ef| G)     prf c∼c′  e          = ρF 
-- lemma-recmapSCtx (G₁ |+| G₂)  prf c∼c′  (inj₁ e)   = ∼α+₁  (lemma-recmapSCtx G₁ prf c∼c′  e)
-- lemma-recmapSCtx (G₁ |+| G₂)  prf c∼c′  (inj₂ e)   = ∼α+₂  (lemma-recmapSCtx G₂ prf c∼c′  e)
-- lemma-recmapSCtx (G₁ |x| G₂)  prf c∼c′  (e₁ , e₂)  = ∼αx   (lemma-recmapSCtx G₁ prf c∼c′  e₁) (lemma-recmapSCtx G₂ prf c∼c′  e₂)
-- lemma-recmapSCtx (|B| S G)    prf c∼c′  (x , e)    = ∼αB   [] (λ y y∉[] → lemma∼swapEquivF (lemma-recmapSCtx G prf c∼c′  e) x y)

-- lemma-recCtx2  : {F H C : Functor}{f : μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H}{c c′ : μ C}
--      → ({e e′ :  ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
--      → c ∼α c′
--      → (e : μ F) → recCtx F f c e ∼α recCtx F f c′ e
-- lemma-recCtx2 {F} {f = f} {c} {c′} prf c∼c′ ⟨ e ⟩ = prf c∼c′ (lemma-recmapSCtx F prf c∼c′ e) 
-- \end{code}


-- \begin{code}
-- lemma-recmapα  : {F H C : Functor}(G : Functor){f : μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H}{c c' : μ C}{e e' : ⟦ G ⟧ (μ F)}
--                → ({e e′ :  ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
--                → ({c : μ C}{S : Sort}{x y : V}{e : ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))} 
--                      → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
--                → c ∼α c'
--                → ∼αF G e e'  
--                → ∼αF G (recmapCtx F G f c e) (recmapCtx F G f c' e')
-- lemma-recmapα (|v| S)        prf _  _    ∼αV         = ∼αV  
-- lemma-recmapα |1|            prf _  _    ∼α1         = ∼α1 
-- lemma-recmapα {F} |R|        prf prf2 c∼c' (∼αR e∼e')
--   = ∼αR (∼αx (lemma-∼αR (prf c∼c'   (lemma-recmapα F prf prf2 c∼c' e∼e'))) (∼αEf e∼e'))     
-- lemma-recmapα (|E| x)        prf _  _    ∼αE         = ρF 
-- lemma-recmapα (|Ef| G)       prf _  _    (∼αEf e∼e') = ∼αEf e∼e'
-- lemma-recmapα (G₁ |+| G₂)    prf prf2  c∼c' (∼α+₁ e∼e')
--   = ∼α+₁  (lemma-recmapα G₁ prf prf2  c∼c' e∼e')  
-- lemma-recmapα (G₁ |+| G₂)    prf prf2 c∼c' (∼α+₂ e∼e')
--   = ∼α+₂  (lemma-recmapα G₂ prf prf2 c∼c' e∼e') 
-- lemma-recmapα (G₁ |x| G₂)    prf prf2 c∼c' (∼αx α₁ α₂)
--   = ∼αx   (lemma-recmapα G₁ prf prf2  c∼c' α₁)
--           (lemma-recmapα G₂ prf prf2  c∼c' α₂)  
-- lemma-recmapα {F} {H} {C} (|B| S G) {f} {c} {c'}  {y , e} {z , e'}
--                prf prf2 c∼c' (∼αB xs fα)  
--   = ∼αB  (fv c ++ fv c' ++ xs)
--          (λ x x∉ → begin
--                      swapF G S y x (recmapCtx F G f c e)
--                    ≈⟨ {!!}  ⟩
--                      recmapCtx F G f (swap S y x c) (swapF G S y x e)
--                    ∼⟨ lemma-recmapSCtx G prf
--                                         {!!}
--                                         (swapF G S y x e) ⟩
--                      recmapCtx F G f c              (swapF G S y x e)
--                    ∼⟨ lemma-recmapα  G prf prf2
--                                       c∼c'
--                                       (fα x (c∉xs++ys→c∉ys {xs = fv c'} (c∉xs++ys→c∉ys {xs = fv c} x∉))) ⟩
--                      recmapCtx F G f c'             (swapF G S z x e')
--                    ∼⟨ lemma-recmapSCtx  G prf {!!}
--                                          (swapF G S z x e') ⟩
--                      recmapCtx F G f (swap S z x c') (swapF G S z x e')
--                    ≈⟨ {!!} ⟩
--                      swapF G S z x (recmapCtx F G f c' e')
--                    ∎)
--      where
--      open ∼F-Reasoning(|Ef| H |x| |Ef| F)(G)
-- \end{code}
  

-- \begin{code}
-- lemma-recCtx  : {F H C : Functor}{f : μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H}{c c' : μ C}{e e' : μ F}
--                → ({e e′ :  ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
--                → ({c : μ C}{S : Sort}{x y : V}{e : ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))} 
--                      → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
--                → c ∼α c'
--                → e ∼α e'  
--                → recCtx F f c e ∼α recCtx F f c' e'
-- lemma-recCtx prf prf2  c∼c' e∼e' = {!  (lemma-recmapα |R| prf prf2 c∼c' e∼e')!} 
-- \end{code}


-- \begin{code}
-- lemma-recCtxα-recCtx  :
--   {C H : Functor}(F : Functor){f : μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H}{c : μ C}{e : μ F}
--   → ({e e′ :  ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))}{c c′ : μ C} → c ∼α c′ → ∼αF F e e′ → f c e ∼α f c′ e′)
--   → ({c : μ C}{S : Sort}{x y : V}{e : ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))} 
--                      → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
--   → recCtxα F f c e ∼α recCtx F f c e
-- \end{code}


-- \begin{code}
-- lemma-recCtxα-recCtx F {c = c} {e} prf prf2 with bindersFreeαElem (fv c) e | lemma-bindersFreeαAlpha (fv c) e
-- ... | e′ , nb | e′∼e = lemma-recCtx prf prf2 ρ e′∼e  
-- \end{code}

