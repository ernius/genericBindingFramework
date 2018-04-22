\begin{code}
module AlphaInduction2 where

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
    → ∃ (λ e' →  ListNotOccurBindF {F} G xs e'                                      ×
                 ((x : V)(x∈be' : ∈bF x G e') → notOccurBindExceptF x G e' (x∈be')) ×
                 ∃ (λ bs → ListOccurBindF G bs e × ((x : V)(x∈be : ∈bF x G e) → x ∈ bs))) 
bindersFreeαElemF (|v| x)        xs e     _
  = e , lemma-bindsv , (λ _ → λ ()) , [] , [] , (λ _ → λ ())
bindersFreeαElemF |1|            xs e     _
  = e , lemma-binds1 , (λ _ → λ ()) , [] , [] , (λ _ → λ ())
bindersFreeαElemF (|E| x)        xs e     _
  = e , lemma-bindsE , (λ _ → λ ()) , [] , [] , (λ _ → λ ())
bindersFreeαElemF {F} (|Ef| G)       xs ⟨ e ⟩ (accEf acce)
  = Data.Product.map  (⟨_⟩) 
                      (Data.Product.map  lemma-bindsEf (Data.Product.map aux ( Data.Product.map id (Data.Product.map lemma-ListOccurBindF-Ef aux2))))
                      (bindersFreeαElemF G xs e acce)
  where
  aux2 : {xs : List V} → ((x₁ : V) → ∈bF x₁ G e → x₁ ∈ xs) →
      (x₁ : V) → ∈bF x₁ {F} (|Ef| G) ⟨ e ⟩ → x₁ ∈ xs
  aux2 f x (∈bFEf x∈) = f x x∈
  aux : {F : Functor}{e : ⟦ G ⟧ (μ G)}
        → ((x₁ : V) (x∈be : ∈bF x₁ G e) →  notOccurBindExceptF x₁ G e x∈be)
        → (x₁ : V) (x∈be : ∈bF x₁ {F} (|Ef| G) ⟨ e ⟩)
        → notOccurBindExceptF x₁ {F} (|Ef| G) (⟨ e ⟩) x∈be
  aux f x (∈bFEf x∈be) = notOccurBExceptEf (f x x∈be)
bindersFreeαElemF {F} |R|        xs ⟨ e ⟩ (accR acce)      
  = Data.Product.map  (⟨_⟩) 
                      (Data.Product.map lemma-bindsR {!!})
                      (bindersFreeαElemF F xs e acce)
bindersFreeαElemF (G₁ |+| G₂)    xs (inj₁ e) (acc+₁ acce)  
  = Data.Product.map  inj₁ 
                      (Data.Product.map lemma-binds+1 {!!})
                      (bindersFreeαElemF G₁ xs e acce)
bindersFreeαElemF (G₁ |+| G₂)    xs (inj₂ e) (acc+₂ acce)  
  = Data.Product.map  inj₂
                      (Data.Product.map lemma-binds+2 {!!})
                      (bindersFreeαElemF G₂ xs e acce)
bindersFreeαElemF {F} (G₁ |x| G₂)    xs (e₁ , e₂) (accx acce₁ acce₂)
  with  bindersFreeαElemF G₁ xs e₁ acce₁
... | (e₁′ , notOccur₁ , _ , b1 , b1lemma1  , b1lemma2) 
  with  bindersFreeαElemF G₂ (xs ++ b1) e₂ acce₂
... | (e₂′ , notOccur₂ , _ , b2 , b2lemma1 ,  b2lemma2)
  = (e₁′ , e₂′) , lemma-binds× notOccur₁ {!!} , {!!} , b1 ++ b2 ,  {!!} , {!!}
bindersFreeαElemF {F} (|B| S G)  xs (x , e) (accB facc)
  with fvF {F} {|B| S G} (x , e) 
... | zs 
  with χ' (xs ++ zs) | lemmaχaux∉ (xs ++ zs)
... | z  | z∉xs++fv
  = Data.Product.map  (λ e' → (z , e'))
                      (Data.Product.map {!!} ( Data.Product.map {!!} {!!})) -- (lemma-bindsB (c∉xs++ys→c∉xs z∉xs++fv))
                      (bindersFreeαElemF G (z ∷ xs) (swapF G S x z e) (facc z))
  where
  aux :  {e : ⟦ G ⟧ (μ F)}
         → ((x₂ : V) (x∈be' : ∈bF x₂ G e) → notOccurBindExceptF x₂ G e x∈be')
         → (x₂ : V) (x∈be' : ∈bF x₂ (|B| S G) (z , e))
         → notOccurBindExceptF x₂ (|B| S G) (z , e) x∈be'
  aux {e} f .z ∈bFB≡     = notOccurBExceptB≡ {!!}
  aux {e} f x (∈bFB x∈)  = notOccurBExceptB (f x x∈) {!!}
\end{code}

