Lambda Calculus

\begin{code}
module Examples.LambdaCalculus where

open import Function hiding (_⟨_⟩_)
open import Data.Nat hiding (fold;_*_)
open import Data.Nat.Properties
open import Data.Sum
open import Data.List
open import Data.Empty
open import Relation.Nullary
open import Data.Product hiding (swap;,_)
open import Relation.Binary hiding (Rel)
open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡ renaming (_⊆_ to _⊆l_)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ;trans to trans≡)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

open import GPBindings
open import Atom
open import Swap
open import FreeVariables
open import Alpha
open import AlphaInduction
open import OccurBind
open import List.ListProperties

infix 8 _·_
\end{code}

\begin{code}
SortλTermVars : Sort
SortλTermVars = 1
\end{code}

%<*lambdacalculus>
\begin{code}
λF : Functor                             -- M,N  :-
λF =      |v| SortλTermVars              --           x
     |+|  |R| |x| |R|                    --      |    M N
     |+|  |B| SortλTermVars |R|          --      |    λ x M
\end{code}
%</lambdacalculus>

%<*lambdacalculusmu>
\begin{code}
λTerm : Set
λTerm = μ λF
\end{code}
%</lambdacalculusmu>

%<*lambdaconstvar>
\begin{code}
v : V → λTerm
v = ⟨_⟩ ∘ inj₁
\end{code}
%</lambdaconstvar>

%<*lambdaconstapp>
\begin{code}
_·_ : λTerm → λTerm → λTerm
M · N = ⟨ inj₂ (inj₁ (M , N)) ⟩
\end{code}
%</lambdaconstapp>

%<*lambdaconstlam>
\begin{code}
ƛ : V → λTerm → λTerm
ƛ n M = ⟨ inj₂ (inj₂ (n , M)) ⟩
\end{code}
%</lambdaconstlam>

\begin{code}
testswap1 : swap SortλTermVars 1 2 (ƛ 1 (v 1 · v 2)) ≡ (ƛ 2 (v 2 · v 1))
testswap1 = refl
\end{code}

Define function by primitive recursion directly

%<*vars>
\begin{code}
vars' : μ λF → ℕ
vars' ⟨ inj₁ _ ⟩               =  1
vars' ⟨ inj₂ (inj₁ (m , n)) ⟩  =  vars' m
                               +  vars' n
vars' ⟨ inj₂ (inj₂ (_ , m)) ⟩  =  vars' m
\end{code}
%</vars>

Now using fold.

%<*varsfold1>
\begin{code}
varsaux : ⟦ λF ⟧ ℕ → ℕ
varsaux (inj₁ _)               = 1
varsaux (inj₂ (inj₁ (m , n)))  = m + n
varsaux (inj₂ (inj₂ (_ , m)))  = m
\end{code}
%</varsfold1>

%<*varsfold2>
\begin{code}
vars : μ λF → ℕ
vars = fold λF varsaux
\end{code}
%</varsfold2>

Prove trivial property of vars function by primitive induction.

%<*varsproof1>
\begin{code}
PVars : μ λF → Set
PVars M = vars M > 0
\end{code}
%</varsproof1>

%<*varsproof2>
\begin{code}
plus>0 : {m n : ℕ} → m > 0 → n > 0 → m + n > 0
plus>0 {m} {n} m>0 n>0 = ≤-steps m n>0
\end{code}
%</varsproof2>

%<*proof'>
\begin{code}
provePVars' : (M : μ λF) → PVars M
provePVars' ⟨ inj₁ x                 ⟩  = s≤s z≤n
provePVars' ⟨ inj₂ (inj₁ ( M  , N )) ⟩  = plus>0 (provePVars' M) (provePVars' N)
provePVars' ⟨ inj₂ (inj₂ (_ ,  M))   ⟩  = provePVars' M
\end{code}
%</proof'>

%<*proof>
\begin{code}
provePVars : (M : μ λF) → PVars M
provePVars = foldInd λF PVars proof
   where
   proof : (e : ⟦ λF ⟧ (μ λF)) → fih λF PVars e → PVars ⟨ e ⟩
   proof (inj₁ x)                tt           = s≤s z≤n
   proof (inj₂ (inj₁ (M  , N)))  (ihM , ihN)  = plus>0 ihM ihN
   proof (inj₂ (inj₂ (_  , M)))  ihM          = ihM
\end{code}
%</proof>

Substitiution

\begin{code}
infix 20 _[_≔_]ₙ
infix 20 _[_≔_]
\end{code}


Naive substitution, assuming binders in M not equal x !

In abstraction case we do not check if x ≡ y, we cannot alse because is a iteration principle

%<*substcontext>
\begin{code}
cF =  |v| SortλTermVars |x| |Ef| λF
\end{code}
%</substcontext>

%<*substaux>
\begin{code}
substaux : μ cF → ⟦ λF ⟧ (μ λF) → μ λF
substaux _           (inj₂ (inj₁ (t₁ , t₂)))  = t₁ · t₂
substaux _           (inj₂ (inj₂ (y , t)))    = ƛ y t   
substaux ⟨ x ,  N ⟩  (inj₁ y) with x ≟v y
... | yes _                                   = N
... | no _                                    = v y 
\end{code}
%</substaux>

%<*naivesubst>
\begin{code}
_[_≔_]ₙ : λTerm → V → λTerm → λTerm
M [ x ≔ N ]ₙ  = foldCtx λF substaux (⟨ x , N ⟩) M
\end{code}
%</naivesubst>

%<*subst>
\begin{code}
_[_≔_] : λTerm → V → λTerm → λTerm
M [ x ≔ N ]   = foldCtx-alpha λF substaux (⟨ x , N ⟩) M 
\end{code}
%</subst>

Examples 

\begin{code}
exampleSubstn1 : (ƛ 1 (v 1 · v 2)) [ 2 ≔ v 1 ]ₙ ≡ ƛ 1 (v 1 · v 1)
exampleSubstn1 = refl

exampleSubst1 : (ƛ 1 (v 1 · v 2)) [ 2 ≔ v 1 ] ≡ ƛ 0 (v 0 · v 1)
exampleSubst1 = refl

exampleSubst2 : (ƛ 2 (v 2 · v 3)) [ 3 ≔ v 1 ] ≡ ƛ 0 (v 0 · v 1)
exampleSubst2 = refl
\end{code}

%<*substlemma1>
\begin{code}
lemma-substα  :  {M M′ N : λTerm}{x : V} →  M ∼α M′ → M [ x ≔ N ] ≡ M′ [ x ≔ N ]
lemma-substα {M} {M′} M∼M′
  = lemma-foldCtxα-StrongαCompatible {cF} {λF} {λF} {substaux} M′ M∼M′
\end{code}
%</substlemma1>

\begin{code}
infix 9 （_∙_）_ 
（_∙_）_ = swap {λF} SortλTermVars
\end{code}

%<*substauxswap>
\begin{code}
lemma-substauxSwap : {c : μ cF}{S : Sort}{y z : V}{e : ⟦ λF ⟧ λTerm}
  → substaux (swap S y z c) (swapF λF S y z e)
     ≡
    swap S y z (substaux c e)
\end{code}
%</substauxswap>

\begin{code}
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
  with SortλTermVars ≟S S
... | yes _ with x ≟v w
...         | yes _ with x ≟v y
...                 | yes _  with w ≟v y
...                         | yes _ with z ≟v z
...                                  | yes _ = refl
...                                  | no  z≢z = ⊥-elim (z≢z refl)
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
    | yes _ | yes x≡w  | yes x≡y | no w≢y = ⊥-elim (w≢y (trans≡ (sym x≡w) x≡y))
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  with x ≟v z
...                              | yes x≡z with w ≟v y 
...                                        | yes w≡y = ⊥-elim (x≢y (trans≡ x≡w w≡y))
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  | yes x≡z | no w≢y with w ≟v z
...                                                 | yes w≡z with y ≟v y 
...                                                           | yes _  = refl
...                                                           | no y≢y = ⊥-elim (y≢y refl)
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  | yes x≡z | no w≢y | no  w≢z = ⊥-elim (w≢z (trans≡ (sym x≡w) x≡z))
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  | no  x≢z with w ≟v y 
...                                        | yes w≡y = ⊥-elim (x≢y (trans≡ x≡w w≡y))    
...                                        | no  w≢y with w ≟v z
...                                                  | yes w≡z = ⊥-elim (x≢z (trans≡ x≡w w≡z))    
...                                                  | no w≢z with x ≟v w
...                                                           | yes _ = refl    
...                                                           | no x≢w = ⊥-elim (x≢w x≡w)
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w with SortλTermVars ≟S S
...                   | no  SortλTermVars≢S = ⊥-elim (SortλTermVars≢S SortλTermVars≡S)
...                   | yes _ with x ≟v y
...                           | yes x≡y with w ≟v y
...                                     | yes w≡y = ⊥-elim (x≢w (trans≡ x≡y (sym w≡y)))
...                                     | no  w≢y with w ≟v z
...                                                | yes w≡z with z ≟v y 
...                                                          | yes z≡y = ⊥-elim (x≢w (trans≡ x≡y (trans≡ (sym z≡y) (sym w≡z))))
...                                                          | no z≢y  = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w 
                      | yes _ | yes x≡y | no w≢y   | no w≢z  with z ≟v w
...                                                           | yes z≡w =  ⊥-elim (w≢z (sym z≡w))
...                                                           | no _ =  refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w | yes _ | no x≢y with x ≟v z
...                                                | yes x≡z with w ≟v y
...                                                          | yes w≡y with y ≟v z
...                                                                    | yes y≡z = ⊥-elim (x≢w (trans≡ x≡z (trans≡ (sym y≡z) (sym w≡y))))
...                                                                    | no y≢z = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w | yes _ | no x≢y | yes x≡z | no w≢y with w ≟v z
...                                                                    | yes w≡z = ⊥-elim (x≢w (trans≡ x≡z (sym w≡z)))
...                                                                    | no w≢z with y ≟v w
...                                                                             | yes y≡w =  ⊥-elim (w≢y (sym y≡w))
...                                                                             | no y≢w =  refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w | yes _ | no x≢y | no  x≢z with w ≟v y 
...                                                          | yes w≡y with x ≟v z
...                                                                    | yes x≡z =  ⊥-elim (x≢z x≡z)
...                                                                    | no _ = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w | yes _ | no x≢y | no  x≢z | no w≢y with w ≟v z 
...                                                                    | yes w≡z with x ≟v y
...                                                                              | yes x≡y =  ⊥-elim (x≢y x≡y)
...                                                                              | no _ = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortλTermVars≡S | no  x≢w | yes _ | no x≢y | no  x≢z | no w≢y  | no w≢z with x ≟v w
...                                                                              | yes x≡w =  ⊥-elim (x≢w x≡w)
...                                                                              | no _ = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
    | no  SortλTermVars≢S with x ≟v w
...           | yes x≡w  = refl
...           | no  _    with SortλTermVars ≟S S
...                       | yes SortλTermVars≡S = ⊥-elim (SortλTermVars≢S SortλTermVars≡S)
...                       | no _  = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {e = inj₂ (inj₁ (M , M'))}               = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {e = inj₂ (inj₂ (y , M))}                = refl
\end{code}

%<*swapsubst>
\begin{code}
lemma-[]Swap : {x y z : V}{M N : λTerm}
  →  (（ y ∙ z ） M) [ （ y ∙ z ）ₐ x ≔ （ y ∙ z ） N ]ₙ ≡ （ y ∙ z ） (M [ x ≔ N ]ₙ)
lemma-[]Swap {x} {y} {z} {M} {⟨ N ⟩}
  = lemmaSwapFoldCtxEquiv  {cF} {λF} {λF} {SortλTermVars} {y} {z} {M} {substaux} {⟨ x , ⟨ N ⟩ ⟩} 
       (λ {c} {S} {x} {y} {e} → lemma-substauxSwap {c} {S} {x} {y} {e})
\end{code}
%</swapsubst>

\begin{code}
lemma-substaux  : {e e′ : ⟦ λF ⟧ (μ λF)}{c c′ :  μ cF}
                → c ∼α c′
                → ∼αF λF e e′
                → substaux c e ∼α substaux c′ e′
lemma-substaux {inj₁ y} (∼αR {x , ⟨ N ⟩} {.x , ⟨ N′ ⟩} (∼αx ∼αV (∼αEf N∼N′))) (∼α+₁ ∼αV) 
  with x ≟v y 
... | yes _                                         =  ∼αR N∼N′
... | no _                                          =  ∼αR (∼α+₁ ∼αV)
lemma-substaux _ (∼α+₂ (∼α+₁  (∼αx e∼e′ e∼e′₁)))    =  ∼αR (∼α+₂ (∼α+₁(∼αx e∼e′ e∼e′₁)))
lemma-substaux _ (∼α+₂ (∼α+₂  (∼αB xs e)))          =  ∼αR (∼α+₂ (∼α+₂ (∼αB xs e)))


lemma-substnα′ : {x : V}{M N N′ : λTerm} → N ∼α N′ → M [ x ≔ N ]ₙ ∼α M [ x ≔ N′ ]ₙ
lemma-substnα′ {x} {M} (∼αR N∼N′) = lemma-foldCtx-alpha-Ctx lemma-substaux (∼αR (∼αx ∼αV (∼αEf N∼N′))) M
\end{code}

%<*substlemma2>
\begin{code}
lemma-substα′  :  {x : V}{M N N′ : λTerm} →  N ∼α N′ → M [ x ≔ N ] ∼α M [ x ≔ N′ ]
lemma-substα′ {x} {M} (∼αR N∼N′) 
  = lemma-foldCtxalpha-cxtalpha lemma-substaux (∼αR (∼αx ∼αV (∼αEf N∼N′))) M
\end{code}
%</substlemma2>

\begin{code}
fv2ctx : {x : V}{M N : λTerm} → ListNotOccurBind (x ∷ fv N) M  → ListNotOccurBind (fv {cF} ⟨ x , N ⟩) M
fv2ctx {x} {M} {⟨ N ⟩} nb = nb
\end{code}

%<*lemmanaivesubst>
\begin{code}
lemmaSubsts :  {z : V}{M N : λTerm} → ListNotOccurBind (z ∷ fv N) M → M [ z ≔ N ] ∼α M [ z ≔ N ]ₙ
lemmaSubsts {z} {M} {N} nb
 = lemma-foldCtxAlpha-foldCtx {cF} {λF} λF {substaux} {⟨ z , N ⟩} {M}
      lemma-substaux
      (λ {c} {S} {x} {y} {e} → lemma-substauxSwap {c} {S} {x} {y} {e})
      (fv2ctx {z} {M} {N} nb)
\end{code}
%</lemmanaivesubst>

Naive Substitution Composition

\begin{code}
lemma-substnfv : {M N : λTerm}{x : V} → x ∉ fvS SortλTermVars M → x notOccurBind M → M ≡ M [ x ≔ N ]ₙ
lemma-substnfv {⟨ inj₁ y ⟩}                           {N} {x} x∉fvy _ 
  with x ≟v y
... | yes x≡y = ⊥-elim ((b∉a∷xs→b≢a x∉fvy) x≡y)
... | no  x≢y = refl
lemma-substnfv  {⟨ inj₂ (inj₁ (M , M′)) ⟩}            {N} {x} x∉fv 
                (notOccurBR (notOccurBinj₂ (notOccurBinj₁ (notOccurBx xnbM xnbM′))))
  =  begin≡
       M · M′
     ≡⟨ cong₂ _·_  (lemma-substnfv {M}   (c∉xs++ys→c∉xs x∉fv) xnbM)
                   (lemma-substnfv {M′}  (c∉xs++ys→c∉ys {x} {fvS SortλTermVars  M} x∉fv) xnbM′)   ⟩
       (M [ x ≔ N ]ₙ) · (M′ [ x ≔ N ]ₙ)
     ≡⟨ refl ⟩
       (M · M′) [ x ≔ N ]ₙ
     □
lemma-substnfv  {⟨ inj₂ (inj₂ (y , M)) ⟩}              {N} {x} x∉fv 
                (notOccurBR (notOccurBinj₂ (notOccurBinj₂ (notOccurBB≢ x≢y xnbM))))
  =  begin≡
       ƛ y M
     ≡⟨ cong (ƛ y)  (lemma-substnfv  {M}
                                     (lemma-∉ (sym≢ x≢y) x∉fv)
                                     xnbM)  ⟩  
       ƛ y (M [ x ≔ N ]ₙ)
     ≡⟨ refl ⟩      
        (ƛ y M) [ x ≔ N ]ₙ
     □

lemma-substCompositionV  : {x y z : V}{N L : λTerm}
                         → x ∉ y ∷ fv  L
                         → x notOccurBind L
                         → (v z) [ x ≔ N ]ₙ [ y ≔ L ]ₙ ≡ (v z) [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ 
lemma-substCompositionV {x} {y} {z} {N} {L} x∉yfvL _ with x ≟v z
... | yes x≡z with y ≟v z 
...         | yes y≡z             = ⊥-elim ((b∉a∷xs→b≢a x∉yfvL) (trans≡ x≡z (sym y≡z)))
...         | no  y≢z with x ≟v z
...                   |  yes _    = refl
...                   |  no  x≢z  = ⊥-elim (x≢z x≡z)
lemma-substCompositionV {x} {y} {z} {N} {L} x∉yfvL xnbL
    | no  x≢z with y ≟v z 
...         | yes y≡z
  = lemma-substnfv (lemma∉fvfvS {λF} {SortλTermVars} {L} (b∉a∷xs→b∉xs x∉yfvL)) xnbL
...         | no  y≢z with x ≟v z
...                   |  yes x≡z  = ⊥-elim (x≢z x≡z)
...                   |  no  _    = refl

lemma-substNComposition : {M N L : λTerm}{x y : V}
     → x ∉ y ∷ fv L
     → x notOccurBind L
     → (M [ x ≔ N ]ₙ) [ y ≔ L ]ₙ ≡ (M [ y ≔ L ]ₙ)[ x ≔ N [ y ≔ L ]ₙ ]ₙ
lemma-substNComposition {⟨ inj₁ z                ⟩} {N} {L} {x} {y} x∉y:fvL x∉bL
  = lemma-substCompositionV {x} {y} {z} {N} {L} x∉y:fvL x∉bL
lemma-substNComposition {⟨ inj₂ (inj₁ (M , M'))  ⟩} x∉y:fvL x∉bL
  = cong₂ _·_ (lemma-substNComposition {M} x∉y:fvL x∉bL) (lemma-substNComposition {M'} x∉y:fvL x∉bL)
lemma-substNComposition {⟨ inj₂ (inj₂ (z , M))   ⟩} x∉y:fvL x∉bL
  = cong (ƛ z) (lemma-substNComposition {M} x∉y:fvL x∉bL)
\end{code}

Parallel Reduction

\begin{code}
open import Relation.Relation λTerm renaming (_∘_ to _∘ᵣ_)
infix 7 _⇉n_
\end{code}

\begin{code}
data _⇉n_ : Rel where
  ⇉nv  :  {x : V}
         → v x ⇉n v x
  ⇉nƛ  :  {M N : λTerm}{x : V}
         → M ⇉n N
         → ƛ x M ⇉n ƛ x N
  ⇉n·  :  {M M' N N' : λTerm}
         → M ⇉n M' → N ⇉n N'
         → M · N ⇉n M' · N'
  ⇉nβ :   {M M' N N' : λTerm}{x : V}
         → M ⇉n M' 
         → N ⇉n N'
         → ƛ x M · N ⇉n M' [ x ≔ N' ]ₙ
\end{code}

All lemmas about ⇉n relation must have freshness premises so naive substitution behaves correctly

\begin{code}
lemma⇉nEquiv : {x y : V}{M N : λTerm} → M ⇉n N → （ x ∙ y ） M ⇉n （ x ∙ y ） N
lemma⇉nEquiv  ⇉nv             = ⇉nv
lemma⇉nEquiv  (⇉nƛ M⇉N)       = ⇉nƛ (lemma⇉nEquiv M⇉N)
lemma⇉nEquiv  (⇉n· M⇉M' N⇉N') = ⇉n· (lemma⇉nEquiv M⇉M') (lemma⇉nEquiv N⇉N')
lemma⇉nEquiv  {x} {y} 
             (⇉nβ {M} {M'} {N} {N'} {z} M⇉M' N⇉N') 
  = subst  (λ X → （ x ∙ y ） (ƛ z M · N) ⇉n X) 
           (lemma-[]Swap {z} {x} {y} {M'} {N'}) 
           (⇉nβ (lemma⇉nEquiv M⇉M') (lemma⇉nEquiv N⇉N'))
-- 
FourλTermF =  |Ef| λF |x| |Ef| λF |x| |Ef| λF |x| |Ef| λF 
FourλTerm = μ FourλTermF

BVC : λTerm → Set
BVC M =  ListNotOccurBind (fv M) M
     
BVCC : λTerm → Set
BVCC M = ({y : V}(y∈bM : y ∈b M) → notOccurBindExcept y M y∈bM)

BVCN : λTerm → Set
BVCN M = BVC M × BVCC M

-- Future Church-Rosser development

postulate
  lemma⇉nBinders : {M N : λTerm}{x : V} → x ∈b N → M ⇉n N → x ∈b M
-- lemma⇉nBinders = {!!}

  lemma⇉nNotBinders : {M N : λTerm}{x : V} → x notOccurBind M → M ⇉n N → x notOccurBind N
-- lemma⇉nNotBinders = {!!}

  lemma⇉nListNotBinders : {M N : λTerm}{xs : List V} → ListNotOccurBind xs M → M ⇉n N → ListNotOccurBind xs N
-- lemma⇉nListNotBinders = {!!}

  lemmaSubstsBVCN : {z : V}{M N : λTerm}
                  → BVCN ((ƛ z M) · N)
                  → M [ z ≔ N ] ∼α M [ z ≔ N ]ₙ                  
-- lemmaSubstsBVCN {z} {M} {N} (bvcƛxMN , f) = lemmaSubsts {z} {M} {N} {!!}

  lemma⇉nNotBindersExcept : {M N : λTerm} → M ⇉n N → BVCC M → BVCC N
-- lemma⇉nNotBindersExcept M⇉nN f y∈bN = {!!}

  lemma⇉nBVCN : {M N : λTerm} → BVCN M → M ⇉n N → BVCN N
-- lemma⇉nBVCN BVCNM M⇉nN = {! !}

lemma-⇉SubstN :  {x : V}{M M' N N' : λTerm }
     → ListNotOccurBind (x ∷ fv N') M
     → M ⇉n M' → N ⇉n N'
     → ({y : V}(y∈bM : y ∈b M) → y notOccurBind N)
     → M [ x ≔ N ]ₙ ⇉n M' [ x ≔ N' ]ₙ
lemma-⇉SubstN {x} {⟨ inj₁ y ⟩}                nb ⇉nv              N⇉N' _
  with x ≟v y
... | yes _ =  N⇉N'
... | no  _ =  ⇉nv
lemma-⇉SubstN {x} {⟨ inj₂ (inj₁ (M , P)) ⟩}   nb (⇉n· M⇉M' P⇉P')  N⇉N' f
  = ⇉n·  (lemma-⇉SubstN  (listNotOccurBx₁inv (listNotOccurBinj₁inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))) M⇉M' N⇉N' (f ∘ ∈bFR ∘ ∈bFinj₂ ∘ ∈bFinj₁ ∘  ∈bFx₁))
         (lemma-⇉SubstN (listNotOccurBx₂inv (listNotOccurBinj₁inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))) P⇉P' N⇉N' (f ∘ ∈bFR ∘ ∈bFinj₂ ∘ ∈bFinj₁ ∘  ∈bFx₂))
lemma-⇉SubstN {x} {⟨ inj₂ (inj₁ (⟨ inj₂ (inj₂ (y , M)) ⟩ , P)) ⟩} .{M' [ y ≔ P' ]ₙ} {N} {N'}
                                              nb (⇉nβ {.M} {M'} {.P} {P'} M⇉M' P⇉P')  N⇉N' f
  = subst  (λ X → (ƛ y (M [ x ≔ N ]ₙ)) · (P [ x ≔ N ]ₙ) ⇉n X)
           (sym (lemma-substNComposition  {M'} {P'} {N'} {y} {x} 
                                          (listNotOccurBBinv∉fv (listNotOccurBinj₂inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF (listNotOccurBx₁inv (listNotOccurBinj₁inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))))))) 
                                          (lemma⇉nNotBinders (f (∈bFR (∈bFinj₂ (∈bFinj₁ (∈bFx₁ (∈bFR (∈bFinj₂ (∈bFinj₂ ∈bFB≡)))))))) N⇉N'))) 
           (⇉nβ  (lemma-⇉SubstN (listNotOccurBBinv (listNotOccurBinj₂inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF (listNotOccurBx₁inv (listNotOccurBinj₁inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))))))) M⇉M' N⇉N' (f ∘ ∈bFR ∘ ∈bFinj₂ ∘ ∈bFinj₁ ∘ ∈bFx₁ ∘ ∈bFR ∘ ∈bFinj₂ ∘ ∈bFinj₂ ∘ ∈bFB))
                 (lemma-⇉SubstN (listNotOccurBx₂inv (listNotOccurBinj₁inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))) P⇉P' N⇉N' (f ∘ ∈bFR ∘ ∈bFinj₂ ∘ ∈bFinj₁ ∘  ∈bFx₂)))
lemma-⇉SubstN {x} {⟨ inj₂ (inj₂ (y , M)) ⟩}   nb (⇉nƛ M⇉M')       N⇉N' f
  = ⇉nƛ (lemma-⇉SubstN (listNotOccurBBinv (listNotOccurBinj₂inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))) M⇉M' N⇉N' (f ∘ ∈bFR ∘ ∈bFinj₂ ∘ ∈bFinj₂ ∘ ∈bFB))

_* : λTerm → λTerm
⟨ inj₁ x                                      ⟩ *  = v x
⟨ inj₂ (inj₁ (⟨ inj₁ x               ⟩ , N))  ⟩ *  = v x                         · N *
⟨ inj₂ (inj₁ (⟨ inj₂ (inj₁ (M , M′)) ⟩ , N))  ⟩ *  = ⟨ inj₂ (inj₁ (M , M′)) ⟩ *  · N *
⟨ inj₂ (inj₁ (⟨ inj₂ (inj₂ (x , M )) ⟩ , N))  ⟩ *  = (M *) [ x ≔ N * ]ₙ
⟨ inj₂ (inj₂ (x , M))                         ⟩ *  = ƛ x (M *)

lemmaBindersβbinder  : {M N : λTerm}{y : V}
       → BVCC (ƛ y M · N) → y notOccurBind M
lemmaBindersβbinder f with f (∈bFR (∈bFinj₂ (∈bFinj₁ (∈bFx₁ (∈bFR (∈bFinj₂ (∈bFinj₂ ∈bFB≡)))))))
lemmaBindersβbinder f | notOccurBExceptR (notOccurBExceptinj₂ (notOccurBExceptinj₁ (notOccurBExceptx₁ (notOccurBExceptR (notOccurBExceptinj₂ (notOccurBExceptinj₂ (notOccurBExceptB≡ y∉bM)))) _))) = y∉bM

lemmaBindersβ  : {M N : λTerm}{y : V}
       → BVCC (ƛ y M · N) → {x : V} → x ∈b M → x notOccurBind N
lemmaBindersβ f x∈ with f (∈bFR (∈bFinj₂ (∈bFinj₁ (∈bFx₁ (∈bFR (∈bFinj₂ (∈bFinj₂ (∈bFB x∈))))))))
lemmaBindersβ f x∈ | notOccurBExceptR (notOccurBExceptinj₂ (notOccurBExceptinj₁ (notOccurBExceptx₁ nbe xnotOccurBindM))) = xnotOccurBindM 

lemmaBinders⇉β : {M N M' N' : λTerm}{y : V}
       → BVCC (ƛ y M · N)
       → M ⇉n M' → N ⇉n N'
       → {x : V} → x ∈b M' → x notOccurBind N'
lemmaBinders⇉β f M⇉M' N⇉N' x∈bM' =  lemma⇉nNotBinders (lemmaBindersβ f (lemma⇉nBinders x∈bM' M⇉M')) N⇉N'

postulate 
  lemma-⇉nFree : {M N : λTerm} → M ⇉n N → fv N ⊆l fv M
-- lemma-⇉nFree = {!!}

  lemma-⇉nFree* : {M : λTerm} → fv (M *) ⊆l fv M
-- lemma-⇉nFree* = {!!}

  lemma* : {M N : λTerm}
       → BVCN M
       → M ⇉n N → N ⇉n M *
-- lemma*  _          ⇉nv                      = ⇉nv
-- lemma*  (nb , b≢)  (⇉nƛ M⇉N)                = ⇉nƛ  (lemma* ({!listNotOccurBBinv (listNotOccurBinj₂inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nb)))!}  , {!!}) M⇉N)
-- lemma*  {⟨ inj₂ (inj₁ (⟨ inj₁ x ⟩ , N)) ⟩}
--         (nb , b≢)  (⇉n· M⇉M' N⇉N')          = ⇉n·  (lemma* ({!!} , (λ {(∈bFR (∈bFinj₁ ()))})) M⇉M')
--                                                    (lemma* ({!!} , {!!}) N⇉N')
-- lemma*  {⟨ inj₂ (inj₁ (⟨ inj₂ (inj₁ (M , P)) ⟩ , N)) ⟩}
--         (nb , b≢)  (⇉n· M⇉M' N⇉N')          = ⇉n·  (lemma* ({!!} , {!!}) M⇉M') 
--                                                    (lemma* ({!!} , {!!}) N⇉N')
-- lemma*  {⟨ inj₂ (inj₁ (⟨ inj₂ (inj₂ (x , M)) ⟩ , N)) ⟩}
--         (nb , b≢)  (⇉n· (⇉nƛ M⇉M') N⇉N')    = ⇉nβ  (lemma* ({!!} , {!!}) M⇉M') 
--                                                    (lemma* ({!!} , {!!}) N⇉N')   
-- lemma*  (nb , b≢)  (⇉nβ {M = M} {N = N}{x = y} M⇉M' N⇉N')  
--   = lemma-⇉SubstN  (lemma-binds:cons (lemma⇉nNotBinders (lemmaBindersβbinder b≢) M⇉M') (lemma-binds⊆ (lemma-⇉nFree* {N}) (lemma⇉nListNotBinders (listNotOccurBBinv (listNotOccurBinj₂inv (listNotOccurBinj₂inv  (lemmalistNotOccurBindFR→ListNotOccurBindF  (listNotOccurBx₁inv (listNotOccurBinj₁inv (listNotOccurBinj₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF (lemma-binds++r {xs = fv (ƛ y M)} nb))))))))) M⇉M')))
--                    (lemma* ({!!} , {!!}) M⇉M')
--                    (lemma* ({!!} , {!!}) N⇉N')
--                    (lemmaBinders⇉β b≢ M⇉M' N⇉N') 

diamBVC⇉n :  {M N P : λTerm} → BVCN M 
          → M ⇉n N → M ⇉n P → ∃ (λ R → N ⇉n R × P ⇉n R)
diamBVC⇉n {M} bvc M⇉N M⇉P = M * , lemma* bvc M⇉N , lemma* bvc M⇉P
\end{code}

Next postulate could be done as started in AlphaInduction3 file, all binders distinct, and is used only for Church-Rosser future development.

\begin{code}
postulate
  lemma-bindersFreeα-BindersAll≢ : {F : Functor}(xs : List V)(e : μ F) 
    → ({x : V}(x∈be' : x ∈b (bindersFreeα xs e)) → notOccurBindExcept x (bindersFreeα xs e) (x∈be')) 
\end{code}

\begin{code}
bvcTerm : λTerm → λTerm
bvcTerm = bindersFreeα []

lemma-bvcTermα : (M : λTerm) → bvcTerm M ∼α M
lemma-bvcTermα M = lemma-bindersFreeα-α [] M

lemmaBVC-bvcTerm : (M : λTerm) → BVC (bvcTerm M)
lemmaBVC-bvcTerm  M = lemma-bindersFreeα-FV∉b [] M

lemmaBVCC-bvcTerm : (M : λTerm) → BVCC (bvcTerm M)
lemmaBVCC-bvcTerm M = lemma-bindersFreeα-BindersAll≢ [] M

lemmasBVCN : (M : λTerm) → BVCN (bvcTerm M)
lemmasBVCN M = (lemmaBVC-bvcTerm M) , (lemmaBVCC-bvcTerm M) 

postulate 
  lemma-⇉nleftα : {M M' N : λTerm}
    → BVCN M → BVCN M' 
    → M' ∼α M
    → M ⇉n N → ∃ (λ N' → M' ⇉n N' × N' ∼α N)
-- lemma-⇉nleftα  BVCNM BVCM' 
--                (∼αR (∼α+₁ (∼αV {x})))                            
--                ⇉nv 
--   = v x , ⇉nv , ∼αR (∼α+₁ ∼αV)
-- lemma-⇉nleftα  BVCNM BVCM' 
--                (∼αR (∼α+₂ (∼α+₂ {e = y , N} {x , M} (∼αB xs f))))  
--                (⇉nƛ M⇉nM') 
--   with lemma∼Bswap {S = SortλTermVars} {y} {x} {N} {M} (∼αB xs f)
-- ... | （yx）N∼M
--   with lemma-⇉nleftα {!!} {!!} （yx）N∼M  M⇉nM'
-- ... | N' , （yx）N⇉nN' , N'∼N 
--   = {! （yx）M'∼M!}
-- lemma-⇉nleftα BVCNM BVCM' M'∼M (⇉n· M⇉nN M⇉nN₁) = {!!}
-- lemma-⇉nleftα BVCNM BVCM' M'∼M (⇉nβ M⇉nN M⇉nN₁) = {!!}
\end{code}


-- Another approach

\begin{code}
infix 7 _⇉_

_⇉_ : Rel
M ⇉ N = ∃ (λ M' → M ∼α M' × BVCN M' × ∃ (λ N' → N' ∼α N × M' ⇉n N'))
\end{code}

\begin{code}
lemma-⇉rightα : {M N P : λTerm} → M ⇉ N → N ∼α P → M ⇉ P
lemma-⇉rightα  (M' , M∼M' , BVCM' , N' , N'∼N , M'⇉N') N∼P 
  = M' , M∼M' , BVCM' , N' , τ N'∼N N∼P , M'⇉N'

lemma-⇉leftα : {M N P : λTerm} → P ∼α M → M ⇉ N → P ⇉ N
lemma-⇉leftα P∼M (M' , M∼M' , BVCM' , N' , N'∼N , M'⇉N') 
  = M' , τ P∼M M∼M' , BVCM' , N' , N'∼N , M'⇉N' 

ρ⇉n : Reflexive (_⇉n_)
ρ⇉n {⟨ inj₁ x ⟩}               = ⇉nv
ρ⇉n {⟨ inj₂ (inj₁ (M , N)) ⟩}  = ⇉n· ρ⇉n ρ⇉n
ρ⇉n {⟨ inj₂ (inj₂ (x , M)) ⟩}  = ⇉nƛ ρ⇉n

ρ⇉ : Reflexive (_⇉_)
ρ⇉ {M} = M' , σ M'∼M , BVCNM' , M' , M'∼M , ρ⇉n 
  where
  M' = bvcTerm M
  M'∼M = lemma-bvcTermα M
  BVCNM' = lemmasBVCN M

diam⇉ : diamond (_⇉_)
diam⇉  {M} {N} {P} 
       (M' ,  M∼M'   , BVCM'   , N' , N'∼N , M'⇉nN')
       (M'' , M∼M''  , BVCM''  , P' , P'∼P , M''⇉nP') 
  with lemma-⇉nleftα BVCM'' BVCM' (τ (σ M∼M') M∼M'') M''⇉nP'  
... | P'' , M'⇉nP'' , P''∼P'     
  with diamBVC⇉n BVCM' M'⇉nN' M'⇉nP''
... | R , N'⇉nR , P''⇉nR
  =  R                                                                          , 
     (N'   , σ N'∼N             , lemma⇉nBVCN BVCM' M'⇉nN'   , R , ρ , N'⇉nR )  ,  
     (P''  , σ (τ P''∼P' P'∼P)  , lemma⇉nBVCN BVCM' M'⇉nP''  , R , ρ , P''⇉nR)
\end{code}


Ctx can be done generically

\begin{code}
data ctx (r : Rel) : Rel where
  ctxinj : ∀ {t t'}       → r t t'        → ctx r t t'
  ctx·l  : ∀ {t₁ t₁' t₂}  → ctx r t₁ t₁'  → ctx r (t₁ · t₂)   (t₁' · t₂)
  ctx·r  : ∀ {t₁ t₂ t₂'}  → ctx r t₂ t₂'  → ctx r (t₁ · t₂)   (t₁ · t₂')
  ctxƛ   : ∀ {x t₁ t₁'}   → ctx r t₁ t₁'  → ctx r (ƛ x t₁)    (ƛ x t₁')

infix 1 _▹n_ 
data _▹n_ : Rel where
  ▹βn  :  {M N : λTerm}{x : V}
      →  ƛ x M · N ▹n M [ x ≔ N ]ₙ

infix 1 _▹_ 
data _▹_ : Rel where
  ▹β  :  {M N : λTerm}{x : V}
      →  ƛ x M · N ▹ M [ x ≔ N ]

infix 4 _→βn_
_→βn_ : Rel
_→βn_ = ctx _▹n_

BVCNRel : Rel → Rel
BVCNRel R M N = BVCN M × R M N

-- lemma▹n⊆▹ : BVCNRel _▹n_ ⊆ (_▹_ ∘ᵣ _∼α_)
-- lemma▹n⊆▹ (BVCN , M▹nN) = {!!} 

infix 4 _→βn*_
_→βn*_ : Rel
_→βn*_ = star _→βn_

infix 4 _→β_
_→β_ : Rel
M →β N = ∃ (λ M' → M ∼α M' × BVCN M' × ∃ (λ N' → N' ∼α N × M' →βn N')) 

-- Real one
infix 4 _→βR_
_→βR_ : Rel
M →βR N = ∃ (λ M' → M ∼α M' × ∃ (λ N' → N' ∼α N × (ctx _▹_) M' N')) 

postulate
  lemma→β⊆→βR : _→β_ ⊆ _→βR_
-- lemma→β⊆→βR (M' , M∼M' , BVCM' , N' , N'∼N , M'→βnN') = M' , M∼M' , N' , N'∼N , {!!} 

  lemma→βR⊆→β : _→βR_ ⊆ _→β_
-- lemma→βR⊆→β (M' , M∼M' , N' , N'∼N , M'→βRN') = {!!}

infix 4 _→α_ 
_→α_ : Rel
_→α_ = _→β_ ∪ _∼α_

infix 4 _→α*_
_→α*_ : Rel
_→α*_ = star _→α_

lemmaBVCN→βn⊆→β : BVCNRel _→βn_ ⊆ _→β_
lemmaBVCN→βn⊆→β {M} {N} (BVCNM , M→βnN) = M , ρ , BVCNM , N , ρ , M→βnN 

infix 4 _→β*_
_→β*_ : Rel
_→β*_ = star _→β_

lemma→α*α : {M M' N N' : λTerm} → M' ∼α M → N ∼α N' → M →α* N → M' →α* N'
lemma→α*α M'∼M N∼N' refl                 = just (inj₂ (τ M'∼M N∼N'))
lemma→α*α M'∼M N∼N' (just M→αN)          = trans (trans (just (inj₂ M'∼M)) (just M→αN)) (just (inj₂ N∼N'))
lemma→α*α M'∼M N∼N' (trans M→α*N N→α*P)  = trans (lemma→α*α M'∼M ρ M→α*N) (lemma→α*α ρ N∼N' N→α*P)

postulate
  lemma-BVCN→βn* : {M N : λTerm} → BVCN M → M →βn* N → BVCN N
-- lemma-BVCN→βn* = {!!}

lemmaBVCN→βn*⊆→β* : {M N : λTerm} → BVCN M → M →βn* N → M →β* N
lemmaBVCN→βn*⊆→β* BVCM refl                   = refl
lemmaBVCN→βn*⊆→β* BVCM (just M→βnN)           = just (lemmaBVCN→βn⊆→β (BVCM , M→βnN))
lemmaBVCN→βn*⊆→β* BVCM (trans M→βn*N N→βn*P)  = trans (lemmaBVCN→βn*⊆→β* BVCM M→βn*N) (lemmaBVCN→βn*⊆→β* (lemma-BVCN→βn* BVCM M→βn*N) N→βn*P)

lemma→βn*ƛ : {x : V}{M N : λTerm} → M →βn* N → ƛ x M →βn* ƛ x N
lemma→βn*ƛ refl                 = refl
lemma→βn*ƛ (just M→βnN)         = just (ctxƛ M→βnN)
lemma→βn*ƛ (trans M→βnN N→βnP)  = trans (lemma→βn*ƛ M→βnN) (lemma→βn*ƛ N→βnP)

lemma→βn*·l : {M M' N : λTerm} → M →βn* M' → (M · N) →βn* (M' · N)
lemma→βn*·l refl                 = refl
lemma→βn*·l (just M→βnN)         = just (ctx·l M→βnN) 
lemma→βn*·l (trans M→βnN N→βnP)  = trans (lemma→βn*·l M→βnN) (lemma→βn*·l N→βnP)

lemma→βn*·r : {M N N' : λTerm} → N →βn* N' → (M · N) →βn* (M · N')
lemma→βn*·r refl                 = refl
lemma→βn*·r (just M→βnN)         = just (ctx·r M→βnN) 
lemma→βn*·r (trans M→βnN N→βnP)  = trans (lemma→βn*·r M→βnN) (lemma→βn*·r N→βnP)

lemma→βn*· : {M M' N N' : λTerm} → M →βn* M' → N →βn* N' → (M · N) →βn* (M' · N')
lemma→βn*· M→βn*M' N→βn*N' = trans (lemma→βn*·l M→βn*M') (lemma→βn*·r N→βn*N')

lemma→βn*β : {x : V}{M M' N N' : λTerm} → M →βn* M' → N →βn* N' → ((ƛ x M) · N) →βn* (M' [ x ≔ N' ]ₙ)
lemma→βn*β M→βn*M' N→βn*N' =  trans (lemma→βn*· (lemma→βn*ƛ M→βn*M') N→βn*N') (just (ctxinj ▹βn))

lemma→βn⊆⇉n : _→βn_ ⊆ _⇉n_
lemma→βn⊆⇉n (ctxinj ▹βn)  = ⇉nβ  ρ⇉n ρ⇉n
lemma→βn⊆⇉n (ctx·l r)     = ⇉n·  (lemma→βn⊆⇉n r) ρ⇉n
lemma→βn⊆⇉n (ctx·r r)     = ⇉n·  ρ⇉n (lemma→βn⊆⇉n r) 
lemma→βn⊆⇉n (ctxƛ r)      = ⇉nƛ  (lemma→βn⊆⇉n r)

-- open ∼-Reasoning(λF)

-- lemma-λxMN⇉M[x:=N] : (M N : λTerm)(x : V) → ƛ x M · N ⇉ M [ x ≔ N ] 
-- lemma-λxMN⇉M[x:=N] M N x 
--   with bvcTerm (ƛ x M · N) | lemma-bvcTermα (ƛ x M · N) | lemmaBVC-bvcTerm (ƛ x M · N) | lemmaBVCC-bvcTerm (ƛ x M · N)
-- ...  | ⟨ (inj₂ (inj₁ (  ⟨ inj₂ (inj₂ (y , M')) ⟩  , N'))) ⟩  
--      | (∼αR (∼α+₂ (∼α+₁ (∼αx (∼αR (∼α+₂ (∼α+₂ (∼αB xs f))))  N'∼N)))) 
--      | bvc | bvcc
--   =  M' [ y ≔ N' ]ₙ          , 
--      ⇉nβ ρ⇉n ρ⇉n             ,
--      (begin
--           M'  [ y ≔ N'  ]ₙ
--         ∼⟨ σ (lemmaSubsts {y} {M'} {N'} {!!}) ⟩
--           M'  [ y ≔ N'  ]
--         ∼⟨  {!!}  ⟩
--           (swap SortλTermVars y x M') [ x ≔ N' ]
--         ∼⟨ lemma-substα′ {x} {swap SortλTermVars y x M'} {N'} {N} N'∼N ⟩
--           (swap SortλTermVars y x M') [ x ≔ N  ]
--         ≈⟨ lemma-substα {swap SortλTermVars y x M'} {M} {N} {x} (lemma∼Bswap {x = y} {x} {M'} {M} (∼αB xs f)) ⟩
--           M   [ x ≔ N   ]
--      ∎)                     

-- lemma→α⊆⇉ (inj₁ (ctxinj (▹β {M} {N} {x})))  = lemma-λxMN⇉M[x:=N] M N x
-- lemma→α⊆⇉ (inj₁ (ctx·l M→αM'))              = lemma-⇉· (lemma→α⊆⇉  (inj₁ M→αM')) ρ⇉
-- lemma→α⊆⇉ (inj₁ (ctx·r N→αN'))              = lemma-⇉· ρ⇉ (lemma→α⊆⇉  (inj₁ N→αN')) 
-- lemma→α⊆⇉ (inj₁ (ctxƛ M→αM'))               = lemma-⇉λ (lemma→α⊆⇉  (inj₁ M→αM'))
-- lemma→α⊆⇉ (inj₂ (∼αR f))                    = lemma-⇉rightα ρ⇉ (∼αR f) 

lemma⇉n⊆→βn* : _⇉n_ ⊆ _→βn*_
lemma⇉n⊆→βn* ⇉nv              = refl
lemma⇉n⊆→βn* (⇉nƛ M⇉M')       = lemma→βn*ƛ (lemma⇉n⊆→βn* M⇉M')
lemma⇉n⊆→βn* (⇉n· M⇉M' N⇉N')  = lemma→βn*· (lemma⇉n⊆→βn* M⇉M') (lemma⇉n⊆→βn* N⇉N')
lemma⇉n⊆→βn* (⇉nβ M⇉M' N⇉N')  = lemma→βn*β (lemma⇉n⊆→βn* M⇉M') (lemma⇉n⊆→βn* N⇉N')

postulate
  lemma-CR⇉n : cr (_⇉n_)
-- lemma-CR⇉n = diamond-cr {!diamBVC⇉n!} --

lemma-CR→βn : cr _→βn_
lemma-CR→βn = cr-⊆ lemma→βn⊆⇉n lemma⇉n⊆→βn* lemma-CR⇉n

lemma→β⊆⇉ : _→β_ ⊆ _⇉_
lemma→β⊆⇉ (M' , M∼M' , BVCNM' , N' , N'∼N , M'→βN') 
  = M' , M∼M' , BVCNM' , N' , N'∼N , lemma→βn⊆⇉n M'→βN'

lemma∼α⊆⇉ : _∼α_ ⊆ _⇉_
lemma∼α⊆⇉ {M} {N} M∼N =  M' , σ M'∼M , BVCNM' ,  M' , τ M'∼M M∼N , ρ⇉n
  where
  M' = bvcTerm M
  M'∼M = lemma-bvcTermα M
  BVCNM' = lemmasBVCN M

lemma→α⊆⇉ : _→α_ ⊆ _⇉_
lemma→α⊆⇉ (inj₁ M→βN)  = lemma→β⊆⇉ M→βN
lemma→α⊆⇉ (inj₂ M∼N)   = lemma∼α⊆⇉ M∼N

lemma→β⊆→α :  _→β_ ⊆ _→α_
lemma→β⊆→α = inj₁

lemma⇉⊆→α* : _⇉_ ⊆ _→α*_
lemma⇉⊆→α* {M} {N} (M' , M∼M' , BVCNM' , N' , N'∼N , M'⇉nN') 
  = lemma→α*α M∼M' N'∼N (mon-star lemma→β⊆→α (lemmaBVCN→βn*⊆→β* BVCNM' (lemma⇉n⊆→βn* M'⇉nN'))) 

lemma-CR⇉ : cr _⇉_
lemma-CR⇉ = diamond-cr diam⇉

lemma-CR→β : cr _→α_
lemma-CR→β = cr-⊆ lemma→α⊆⇉ lemma⇉⊆→α* lemma-CR⇉
\end{code}



