\begin{code}
module Fresh where

open import GPBindings
open import Swap

open import Data.Unit
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}

%<*fresh>
\begin{code}
data freshF (S : Sort)(x : V){F : Functor} : 
            (G : Functor) → ⟦ G ⟧ (μ F) → Set where
   freshV≢   : {y : V}{S' : Sort} 
             → x ≢ y              → freshF S x (|v| S')    y
   freshV≢S  : {y : V}{S' : Sort} 
             → S' ≢ S             → freshF S x (|v| S')    y
   fresh1    :                      freshF S x |1|         tt
   freshE    : {B : Set}{b : B}   → freshF S x (|E| B) b
   freshEf   : {G : Functor}{e : ⟦ G ⟧ (μ G)}
             → freshF S x G e     → freshF S x (|Ef| G )   ⟨ e ⟩
   freshR    : {e : ⟦ F ⟧ (μ F)}
             → freshF S x F e     → freshF S x |R|         ⟨ e ⟩            
   freshinj₁ : {F₁ F₂ : Functor}{e : ⟦ F₁ ⟧ (μ F)}
             → freshF S x F₁ e    → freshF S x (F₁ |+| F₂)  (inj₁ e) 
   freshinj₂ : {F₁ F₂ : Functor}{e : ⟦ F₂ ⟧ (μ F)}
             → freshF S x F₂ e    → freshF S x (F₁ |+| F₂)  (inj₂ e) 
   freshx    : {F₁ F₂ : Functor}{e₁ : ⟦ F₁ ⟧ (μ F)}{e₂ : ⟦ F₂ ⟧ (μ F)}
             → freshF S x F₁ e₁
             → freshF S x F₂ e₂   → freshF S x (F₁ |x| F₂)  (e₁ , e₂) 
   freshb≡   : {G : Functor}{e : ⟦ G ⟧ (μ F)}
                                  → freshF S x (|B| S G)    (x , e)
   freshb    : {G : Functor}{S' : Sort}{e : ⟦ G ⟧ (μ F)}{y : V}
             → freshF S x G e     → freshF S x (|B| S' G)   (y , e)

\end{code}

%<*freshsignature>
\begin{code}
fresh : (S : Sort)(x : V){F : Functor} → (μ F) → Set
\end{code}
%</freshsignature>

\begin{code}
fresh S x = freshF S x |R|
\end{code}
%</fresh>

\begin{code}
postulate
  lemmaSwapF# : {F G : Functor}{S : Sort}{x y : V}{e  : ⟦ G ⟧ (μ F)}
        → freshF S y G e
        → freshF S x G (swapF G S x y e)
--lemmaSwapF# = {!!}

  lemmaSwapF#≢→ : {F G : Functor}{S : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → x ≢ y → x ≢ z 
        → freshF S x G (swapF G S y z e)
        → freshF S x G e
--lemmaSwapF#≢→ = {!!}

  lemmaSwapF#≢← : {F G : Functor}{S : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → x ≢ y → x ≢ z 
        → freshF S x G e
        → freshF S x G (swapF G S y z e)
--lemmaSwapF#≢← = {!!}

  lemmaSwapF#≢S→ : {F G : Functor}{S S' : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → S ≢ S'      
        → freshF S x G (swapF G S' y z e)
        → freshF S x G e
--lemmaSwapF#≢S→ = {!!}

  lemmaSwapF#≢S← : {F G : Functor}{S S' : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → S ≢ S'      
        → freshF S x G e
        → freshF S x G (swapF G S' y z e)
--lemmaSwapF#≢S← = {!!}
\end{code}
