\begin{code}
module Permutation where

open import Atom

open import Data.List
open import Data.Product
open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary
open import Data.Empty

Π = List (Atom × Atom)  
--
ι : List Atom
ι = [] 
--
_⁻¹ : Π → Π
_⁻¹ = reverse
--
\end{code}

%<*atomPermutation>
\begin{code}
_∙ₐ_ : Π → Atom → Atom
π ∙ₐ a = foldr (λ s b → （ proj₁ s ∙ proj₂ s ）ₐ b) a π 
\end{code}
%</atomPermutation>

\begin{code}
atoms : Π → List Atom
atoms π = foldr (λ p r → proj₁ p ∷ proj₂ p ∷ r) [] π
--
lemmaπ∙ₐ≡ : {a : Atom}{π : Π} → a ∉ atoms π → π ∙ₐ a ≡ a
lemmaπ∙ₐ≡ {a} {[]}           a∉π  = refl
lemmaπ∙ₐ≡ {a} {(b , c) ∷ π}  a∉b,c∷π 
  rewrite lemmaπ∙ₐ≡ {a} {π} (λ a∈π → a∉b,c∷π (there (there a∈π))) 
  with a ≟ₐ b 
... | no _ with a ≟ₐ c
...        | no _                 = refl
lemmaπ∙ₐ≡ {a} {(b , .a) ∷ π}  a∉b,a∷π 
    | no _ | yes refl             
    = ⊥-elim (a∉b,a∷π (there (here refl)))
lemmaπ∙ₐ≡ {a} {(.a , c) ∷ π}  a∉a,c∷π   
    | yes refl                    
    = ⊥-elim (a∉a,c∷π (here refl))
--
lemmaππ∙ₐinj : {a b : Atom}{π : Π} → a ≢ b → π ∙ₐ a ≢ π ∙ₐ b
lemmaππ∙ₐinj {a} {b} {[]}           a≢b = a≢b
lemmaππ∙ₐinj {a} {b} {(c , d) ∷ π}  a≢b = lemma∙ₐinj (lemmaππ∙ₐinj {π = π} a≢b)
\end{code}
