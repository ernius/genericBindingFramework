System F, Nominal syntax

\begin{code}
module Examples.SystemF where

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary hiding (Rel)
open import Function
open import Data.Nat hiding (fold;_*_)
open import Data.Nat.Properties
open import Data.List hiding (unfold;[_])
open import Data.List.All
open import Data.Sum
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)
open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡ hiding (_⊆_)

open import GPBindings
open import Atom
open import Swap
open import Fresh
open import FreeVariables
open import Alpha
open import AlphaInduction
open import OccurBind
open import List.ListProperties

SortFTypeVars : Sort
SortFTypeVars = 1

SortFTermVars : Sort
SortFTermVars = 2
\end{code}

%<*systemF>
\begin{code}
tyF : Functor                                      -- t,r :-
tyF =      |v| SortFTypeVars                       --   α
      |+|  |R| |x| |R|                             -- | t → r
      |+|  |B| SortFTypeVars |R|                   -- | ∀ α . t

tF : Functor                                       -- M,N :-
tF =      |v| SortFTermVars                        --   x
     |+|  |R| |x| |R|                              -- | M N
     |+|  |Ef| tyF |x| |B| SortFTermVars |R|       -- | λ x : t . M
     |+|  |R| |x| |Ef| tyF                         -- | M t
     |+|  |B| SortFTypeVars |R|                    -- | Λ α . M
\end{code}
%</systemF>

%<*systemFmuty>
\begin{code}
FType : Set
FType = μ tyF
\end{code}
%</systemFmuty>

%<*systemFmutrm>
\begin{code}
FTerm : Set
FTerm = μ tF
\end{code}
%</systemFmutrm>


\begin{code}
vₜ : V → FType
vₜ = ⟨_⟩ ∘ inj₁

_⟶_ : FType → FType → FType
α ⟶ β = ⟨ inj₂ (inj₁ (α , β)) ⟩  

∀ₜ  : V → FType → FType
∀ₜ x α = ⟨ inj₂ (inj₂ (x , α)) ⟩ 

v : V → FTerm
v = ⟨_⟩ ∘ inj₁

_·_ : FTerm → FTerm → FTerm
M · N = ⟨ inj₂ (inj₁ (M , N)) ⟩ 

ƛ : V → FType → FTerm → FTerm
ƛ n α M = ⟨ inj₂ (inj₂ (inj₁ (α , n , M))) ⟩

_·ₜ_ : FTerm → FType → FTerm
M ·ₜ α = ⟨ inj₂ (inj₂ (inj₂ (inj₁ (M , α)))) ⟩

Λ : V → FTerm → FTerm
Λ α M = ⟨ inj₂ (inj₂ (inj₂ (inj₂ (α , M)))) ⟩

testswap1 : swap SortFTermVars 1 2 (Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 2))) ≡ (Λ 1 (ƛ 2 (vₜ 1) (v 2 · v 1)))
testswap1 = refl

testswap2 : swap SortFTypeVars 1 2 (Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 2))) ≡ (Λ 2 (ƛ 1 (vₜ 2) (v 1 · v 2)))
testswap2 = refl

-- Define function with fold
varsaux : ⟦ tF ⟧ ℕ → ℕ
varsaux (inj₁ n)                            = 1
varsaux (inj₂ (inj₁ (m , n)))               = m + n
varsaux (inj₂ (inj₂ (inj₁ (_ , _ , m))))    = m
varsaux (inj₂ (inj₂ (inj₂ (inj₁ (n , _))))) = n
varsaux (inj₂ (inj₂ (inj₂ (inj₂ (_ , m))))) = m

vars : FTerm → ℕ
vars = fold tF varsaux

-- Prove trivial property of vars function by primitive induction.
PVars : FTerm → Set
PVars M = vars M > 0

ProvePVars : (M : FTerm) → PVars M
ProvePVars = foldInd tF PVars proof
   where
   plus>0 : {m n : ℕ} → m > 0 → n > 0 → m + n > 0
   plus>0 {m} {n} m>0 n>0 = ≤-steps m n>0
   proof : (e : ⟦ tF ⟧ (μ tF)) → fih tF PVars e → PVars ⟨ e ⟩
   proof (inj₁ x)                                 tt         = s≤s z≤n
   proof (inj₂ (inj₁ (⟨ M ⟩ , ⟨ N ⟩)))            (PM , PN)  = plus>0 PM PN
   proof (inj₂ (inj₂ (inj₁ (α , x , ⟨ M ⟩))))     (tt , PM)  = PM
   proof (inj₂ (inj₂ (inj₂ (inj₁ (⟨ M ⟩ , α)))))  (PM , tt)  = PM
   proof (inj₂ (inj₂ (inj₂ (inj₂ (x , ⟨ M ⟩)))))  PM         = PM

examplefresh : fresh SortFTermVars 1 (ƛ 1 (vₜ 1) (v 1 · v 2))
examplefresh = freshR (freshinj₂ (freshinj₂ (freshinj₁ (freshx (freshEf (freshinj₁ (freshV≢S 1≢2))) freshb≡))))
  where
  1≢2 : 1 ≢ 2
  1≢2 = λ ()

examplefv : fvS SortFTermVars (Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 2))) ≡ 2 ∷ []
examplefv = refl

examplefv2 : (fvS SortFTypeVars (Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 2)))) ≡ []
examplefv2 = refl

examplefv3 : fvS SortFTypeVars (ƛ 1 (vₜ 1) (v 1 · v 2)) ≡ 1 ∷ []
examplefv3 = refl
\end{code}

-- substaux :  (x : V)(t : μ tF)
--             → (e : ⟦ tF ⟧ (μ tF)) 
--             → fihα tF (const (μ tF)) e (x ∷ fv SortFTermVars t) 
--             → μ tF
-- substaux x t' (inj₁ y)                              tt     with x ≟v y
-- ... | yes _                                                      = t'
-- ... | no _                                                       = v y 
-- substaux x t' (inj₂ (inj₁ (t₁ , t₂)))               (hi₁ , hi₂)  = proj₁ hi₁ · proj₁ hi₂
-- substaux x t' (inj₂ (inj₂ (inj₁ (ty , y , t))))     ih           = ƛ y ty (proj₁ (proj₂ (proj₂ ih)))
-- substaux x t' (inj₂ (inj₂ (inj₂ (inj₁ (t , ty)))))  ih           = (proj₁ (proj₁  ih)) ·ₜ  ty
-- substaux x t' (inj₂ (inj₂ (inj₂ (inj₂ (α , t)))))   ih           = Λ α (proj₁ (proj₂ ih))

-- _[_≔_] : FTerm → V → FTerm → FTerm
-- t [ x ≔ t' ] = αIteration (x ∷ fv SortFTermVars t') (substaux x t') t

-- substaux : (x : V)(t : μ tF) → ⟦ tF ⟧ (μ tF) → μ tF
-- substaux x t' (inj₁ y) with x ≟v y
-- ... | yes _                                         = t'
-- ... | no _                                          = v y 
-- substaux x t' (inj₂ (inj₁ (t₁ , t₂)))               = t₁ · t₂
-- substaux x t' (inj₂ (inj₂ (inj₁ (ty , y , t))))     = ƛ y ty t
-- substaux x t' (inj₂ (inj₂ (inj₂ (inj₁ (t , ty)))))  = t ·ₜ  ty
-- substaux x t' (inj₂ (inj₂ (inj₂ (inj₂ (α , t)))))   = Λ α t

-- _[_≔_]ₙ : FTerm → V → FTerm → FTerm
-- t [ x ≔ t' ]ₙ  = fold tF (substaux x t') t

-- _[_≔_] : FTerm → V → FTerm → FTerm
-- t [ x ≔ t' ]   = foldα tF (x ∷ fv SortFTermVars t') (substaux x t') t

\begin{code}
infix 11 _[_≔_]ₙ
infix 11 _[_≔_]
\end{code}

%<*substaux>
\begin{code}
cF =  |v| SortFTermVars |x| |Ef| tF

substaux : μ cF → ⟦ tF ⟧ (μ tF) → μ tF
substaux _           (inj₂ (inj₁ (t₁ , t₂)))               = t₁ · t₂
substaux _           (inj₂ (inj₂ (inj₁ (ty , y , t))))     = ƛ y ty t
substaux _           (inj₂ (inj₂ (inj₂ (inj₁ (t , ty)))))  = t ·ₜ  ty
substaux _           (inj₂ (inj₂ (inj₂ (inj₂ (α , t)))))   = Λ α t
substaux ⟨ x ,  N ⟩  (inj₁ y) with x ≟v y
... | yes _                                                = N
... | no _                                                 = v y 
\end{code}
%</substaux>

%<*naivesubst>
\begin{code}
_[_≔_]ₙ : FTerm → V → FTerm → FTerm
M [ x ≔ N ]ₙ  = foldCtx tF substaux (⟨ x , N ⟩) M
\end{code}
%</naivesubst>

%<*subst>
\begin{code}
_[_≔_] : FTerm → V → FTerm → FTerm
M [ x ≔ N ]   = foldCtxα  tF substaux (⟨ x , N ⟩) M 
\end{code}
%</subst>

\begin{code}
-- Examples 
exampleSubstn1 : Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 2)) [ 2 ≔ v 1 ]ₙ ≡ Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 1))
exampleSubstn1 = refl

exampleSubst1 : Λ 1 (ƛ 1 (vₜ 1) (v 1 · v 2)) [ 2 ≔ v 1 ] ≡ Λ 0 (ƛ 0 (vₜ 0) (v 0 · v 1))
exampleSubst1 = refl

exampleSubst2 : Λ 2 (ƛ 2 (vₜ 1) (v 2 · v 3)) [ 3 ≔ v 1 ] ≡ Λ 0 (ƛ 0 (vₜ 1) (v 0 · v 1))
exampleSubst2 = refl

infix 9 （_∙_）_ 
（_∙_）_ = swap {tF} SortFTermVars
\end{code}


%<*substauxBinds>
\begin{code}
lemma-substauxBinds : {c : μ cF}{xs : List V}
  → ListNotOccurBind xs c
  → {e : ⟦ tF ⟧ FTerm}
  → ListNotOccurBindF tF xs e
  → ListNotOccurBind xs (substaux c e)
lemma-substauxBinds {⟨ x , N ⟩} {xs} xs∉xN {inj₁ y}                              xs∉e with x ≟v y
... | yes _ = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₂inv  (lemmalistNotOccurBindFR→ListNotOccurBindF xs∉xN))
... | no  _ = lemma-bindsR xs∉e
lemma-substauxBinds {⟨ x , N ⟩} {xs} xs∉xN {inj₂ (inj₁ (M , P))}                 xs∉e = lemma-bindsR xs∉e
lemma-substauxBinds {⟨ x , N ⟩} {xs} xs∉xN {inj₂ (inj₂ (inj₁ (ty , y , M)))}     xs∉e = lemma-bindsR xs∉e
lemma-substauxBinds {⟨ x , N ⟩} {xs} xs∉xN {inj₂ (inj₂ (inj₂ (inj₁ (M , ty))))}  xs∉e = lemma-bindsR xs∉e
lemma-substauxBinds {⟨ x , N ⟩} {xs} xs∉xN {inj₂ (inj₂ (inj₂ (inj₂ (α , M))))}   xs∉e = lemma-bindsR xs∉e
\end{code}
%</substauxBinds>


%<*substauxSwap>
\begin{code}
lemma-substauxSwap : {c : μ cF}{S : Sort}{y z : V}{e : ⟦ tF ⟧ FTerm}
  →  substaux (swap S y z c) (swapF tF S y z e)
       ≡
     swap S y z (substaux c e)
\end{code}
%</substauxSwap>

\begin{code}
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
  with SortFTermVars ≟S S
... | yes _ with x ≟v w
...         | yes _ with x ≟v y
...                 | yes _  with w ≟v y
...                         | yes _ with z ≟v z
...                                  | yes _ = refl
...                                  | no  z≢z = ⊥-elim (z≢z refl)
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
    | yes _ | yes x≡w  | yes x≡y | no w≢y = ⊥-elim (w≢y (trans (sym x≡w) x≡y))
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  with x ≟v z
...                              | yes x≡z with w ≟v y 
...                                        | yes w≡y = ⊥-elim (x≢y (trans x≡w w≡y))
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  | yes x≡z | no w≢y with w ≟v z
...                                                 | yes w≡z with y ≟v y 
...                                                           | yes _  = refl
...                                                           | no y≢y = ⊥-elim (y≢y refl)
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  | yes x≡z | no w≢y | no  w≢z = ⊥-elim (w≢z (trans (sym x≡w) x≡z))
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes _  | yes x≡w  | no x≢y  | no  x≢z with w ≟v y 
...                                        | yes w≡y = ⊥-elim (x≢y (trans x≡w w≡y))    
...                                        | no  w≢y with w ≟v z
...                                                  | yes w≡z = ⊥-elim (x≢z (trans x≡w w≡z))    
...                                                  | no w≢z with x ≟v w
...                                                           | yes _ = refl    
...                                                           | no x≢w = ⊥-elim (x≢w x≡w)
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w with SortFTermVars ≟S S
...                   | no  SortFTermVars≢S = ⊥-elim (SortFTermVars≢S SortFTermVars≡S)
...                   | yes _ with x ≟v y
...                           | yes x≡y with w ≟v y
...                                     | yes w≡y = ⊥-elim (x≢w (trans x≡y (sym w≡y)))
...                                     | no  w≢y with w ≟v z
...                                                | yes w≡z with z ≟v y 
...                                                          | yes z≡y = ⊥-elim (x≢w (trans x≡y (trans (sym z≡y) (sym w≡z))))
...                                                          | no z≢y  = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w 
                      | yes _ | yes x≡y | no w≢y   | no w≢z  with z ≟v w
...                                                           | yes z≡w =  ⊥-elim (w≢z (sym z≡w))
...                                                           | no _ =  refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w | yes _ | no x≢y with x ≟v z
...                                                | yes x≡z with w ≟v y
...                                                          | yes w≡y with y ≟v z
...                                                                    | yes y≡z = ⊥-elim (x≢w (trans x≡z (trans (sym y≡z) (sym w≡y))))
...                                                                    | no y≢z = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w | yes _ | no x≢y | yes x≡z | no w≢y with w ≟v z
...                                                                    | yes w≡z = ⊥-elim (x≢w (trans x≡z (sym w≡z)))
...                                                                    | no w≢z with y ≟v w
...                                                                             | yes y≡w =  ⊥-elim (w≢y (sym y≡w))
...                                                                             | no y≢w =  refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w | yes _ | no x≢y | no  x≢z with w ≟v y 
...                                                          | yes w≡y with x ≟v z
...                                                                    | yes x≡z =  ⊥-elim (x≢z x≡z)
...                                                                    | no _ = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w | yes _ | no x≢y | no  x≢z | no w≢y with w ≟v z 
...                                                                    | yes w≡z with x ≟v y
...                                                                              | yes x≡y =  ⊥-elim (x≢y x≡y)
...                                                                              | no _ = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
   | yes SortFTermVars≡S | no  x≢w | yes _ | no x≢y | no  x≢z | no w≢y  | no w≢z with x ≟v w
...                                                                              | yes x≡w =  ⊥-elim (x≢w x≡w)
...                                                                              | no _ = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {y} {z} {inj₁ w}                             
    | no  SortFTermVars≢S with x ≟v w
...           | yes x≡w  = refl
...           | no  _    with SortFTermVars ≟S S
...                       | yes SortFTermVars≡S = ⊥-elim (SortFTermVars≢S SortFTermVars≡S)
...                       | no _  = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {e = inj₂ (inj₁ (M , M'))}               = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {e = inj₂ (inj₂ (inj₁ (t , w , M)))}     = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {e = inj₂ (inj₂ (inj₂ (inj₁ (M , t))))}  = refl
lemma-substauxSwap {⟨ x , ⟨ N ⟩ ⟩} {S} {e = inj₂ (inj₂ (inj₂ (inj₂ (α , M))))}  = refl

lemma-[]Swap : {x y z : V}{M N : FTerm}
  → (swap SortFTermVars y z M) [ （ y ∙ z ）ₐ x ≔ swap SortFTermVars y z N ]ₙ
     ≡
    swap SortFTermVars y z (M [ x ≔ N ]ₙ)
lemma-[]Swap {x} {y} {z} {M} {⟨ N ⟩}
  = lemmaSwapFoldCtxEquiv {cF} {tF} {tF} {SortFTermVars} {y} {z} {M} {substaux} {⟨ x , ⟨ N ⟩ ⟩} (λ {c} {S} {x} {y} {e} → lemma-substauxSwap {c} {S} {x} {y} {e})

\end{code}

%<*substlemma1>
\begin{code}
lemma-substα :  {M M′ N : FTerm}{x : V}
                → M ∼α M′ → M [ x ≔ N ] ≡ M′ [ x ≔ N ]
lemma-substα {M} {M′} M∼M′
  = lemma-foldCtxα-StrongαCompatible {cF} {tF} {tF} {substaux} M′ M∼M′
\end{code}
%</substlemma1>

\begin{code}
\end{code}

%<*lemmasubstaux>
\begin{code}
lemma-substaux  : {e e′ : ⟦ tF ⟧ (μ tF)}{c c′ :  μ cF}
                → c ∼α c′
                → ∼αF tF e e′
                → substaux c e ∼α substaux c′ e′
\end{code}
%</lemmasubstaux>

\begin{code}
lemma-substaux {inj₁ y} (∼αR {x , ⟨ N ⟩} {.x , ⟨ N′ ⟩} (∼αx ∼αV (∼αEf N∼N′))) (∼α+₁ ∼αV) 
  with x ≟v y 
... | yes _                                                    =  ∼αR N∼N′
... | no _                                                     =  ∼αR (∼α+₁ ∼αV)
lemma-substaux _ (∼α+₂ (∼α+₁  (∼αx e∼e′ e∼e′₁)))               =  ∼αR (∼α+₂ (∼α+₁  (∼αx e∼e′ e∼e′₁)))
lemma-substaux _ (∼α+₂ (∼α+₂ (∼α+₁ (∼αx e∼e′ e∼e′₁))))         =  ∼αR (∼α+₂ (∼α+₂ (∼α+₁ (∼αx e∼e′ e∼e′₁))))
lemma-substaux _ (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₁ (∼αx e∼e′ e∼e′₁)))))  =  ∼αR (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₁ (∼αx e∼e′ e∼e′₁)))))
lemma-substaux _ (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₂  (∼αB xs x₁)))))      =  ∼αR (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₂  (∼αB xs x₁)))))

lemma-substnα′ :  {x : V}{M N N′ : FTerm}
                  → N ∼α N′ → M [ x ≔ N ]ₙ ∼α M [ x ≔ N′ ]ₙ
lemma-substnα′ {x} {M} (∼αR N∼N′)
  = lemma-foldCtxαCtx lemma-substaux (∼αR (∼αx ∼αV (∼αEf N∼N′))) M
\end{code}

%<*substlemma2>
\begin{code}
lemma-substα′ :  {x : V}{M N N′ : FTerm}
                 → N ∼α N′ → M [ x ≔ N ] ∼α M [ x ≔ N′ ]
lemma-substα′ {x} {M} (∼αR N∼N′)
  = lemma-foldCtxα-cxtα lemma-substaux (∼αR (∼αx ∼αV (∼αEf N∼N′))) M
\end{code}
%</substlemma2>

\begin{code}
fv2ctx : {x : V}{M N : FTerm} → ListNotOccurBind (x ∷ fv N) M  → ListNotOccurBind (fv {cF} ⟨ x , N ⟩) M
fv2ctx {x} {M} {⟨ N ⟩} nb = nb
\end{code}

%<*lemmasubsts>
\begin{code}
lemmaSubsts :  {z : V}{M N : FTerm}
               → ListNotOccurBind (z ∷ fv N) M
               → M [ z ≔ N ] ∼α M [ z ≔ N ]ₙ
lemmaSubsts {z} {M} {N} nb
 = lemma-foldCtxα-foldCtx
      {cF} {tF} tF {substaux} {⟨ z , N ⟩} {M}
      lemma-substaux
      (λ {c} {S} {x} {y} {e} → lemma-substauxSwap {c} {S} {x} {y} {e})
      (fv2ctx {z} {M} {N} nb)
\end{code}
%</lemmasubsts>

\begin{code}
-- {- Previous lemma could also be proved by simple induction on terms -}
-- substα′2 : (x : V)(t t′ t″ : FTerm) → t′ ∼α t″ → t [ x ≔ t′ ] ∼α t [ x ≔ t″ ]
-- substα′2 x t t′ t″ t′∼t″ 
--   with x ∷ fv SortFTermVars t′ | x ∷ fv SortFTermVars t″ | cong (_∷_ x) (lemma∼fv' SortFTermVars t′∼t″)
-- ... | fvt′ | .fvt′ | refl 
--   with proj₁ (bindersFreeαElem fvt′ t)
-- ... | e 
--   = foldInd tF (λ t → t′ ∼α t″ → fold tF (substaux x t′) t ∼α fold tF (substaux x t″) t) substα′aux e t′∼t″
--   where
--   substα′aux  : (e : ⟦ tF ⟧ (μ tF))
--               → fih tF (λ t₁ → t′ ∼α t″ → fold tF (substaux x t′) t₁ ∼α fold tF (substaux x t″) t₁) e
--               → t′ ∼α t″ → fold tF (substaux x t′) ⟨ e ⟩ ∼α fold tF (substaux x t″) ⟨ e ⟩
--   substα′aux (inj₁ y)                                  _            t′∼t″
--       with x ≟v y 
--   ... | yes _ = t′∼t″
--   ... | no  _ = ∼αR (∼α+₁ ∼αV)
--   substα′aux (inj₂ (inj₁ (⟨ t₁ ⟩ , ⟨ t₂ ⟩)))           (hi₁ , hi₂)  t′∼t″
--     = ∼αR (∼α+₂ (∼α+₁ (∼αx (hi₁ t′∼t″) (hi₂ t′∼t″))))
--   substα′aux (inj₂ (inj₂ (inj₁ (ty , x , ⟨ t ⟩))))     (_ , hi)     t′∼t″
--     = ∼αR (∼α+₂ (∼α+₂ (∼α+₁ (∼αx ρF (∼αB [] ( λ c c∉[] → lemma∼swapEquiv2 (hi  t′∼t″) x c)))))) --
--   substα′aux (inj₂ (inj₂ (inj₂ (inj₁ (⟨ t ⟩ , ty)))))  (hi , _)     t′∼t″
--     = ∼αR (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₁ (∼αx (hi t′∼t″) ρF))))) --
--   substα′aux (inj₂ (inj₂ (inj₂ (inj₂ (α , ⟨ t ⟩)))))   hi           t′∼t″
--     = ∼αR (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₂ (∼αB [] (λ c c∉[] → lemma∼swapEquiv2 (hi  t′∼t″) α c)))))) --

-- -- substauxty : (x : V)(ty : FType)
-- --       (e : ⟦ tF ⟧ (μ tF))
-- --       → fihα tF (const (μ tF)) e (x ∷ fv SortFTypeVars ty)
-- --       → μ tF
-- -- substauxty x ty e fihα = {!!}

-- -- _[_≔_]ₜ : FTerm → V → FType → FTerm
-- -- t [ x ≔ ty ]ₜ = αIteration (x ∷ fv SortFTypeVars ty) (substauxty x ty) t

lemma-substnfv : {M N : FTerm}{x : V} → x ∉ fvS SortFTermVars M → x notOccurBind M → M ≡ M [ x ≔ N ]ₙ
lemma-substnfv {⟨ inj₁ y ⟩}                           {N} {x} x∉fvy _ 
  with x ≟v y
... | yes x≡y = ⊥-elim ((b∉a∷xs→b≢a x∉fvy) x≡y)
... | no  x≢y = refl
lemma-substnfv  {⟨ inj₂ (inj₁ (M , M′)) ⟩}            {N} {x} x∉fv 
                (notOccurBR (notOccurBinj₂ (notOccurBinj₁ (notOccurBx xnbM xnbM′))))
  =  begin≡
       M · M′
     ≡⟨ cong₂ _·_  (lemma-substnfv {M}   (c∉xs++ys→c∉xs x∉fv) xnbM)
                   (lemma-substnfv {M′}  (c∉xs++ys→c∉ys {x} {fvS SortFTermVars  M} x∉fv) xnbM′)   ⟩
       (M [ x ≔ N ]ₙ) · (M′ [ x ≔ N ]ₙ)
     ≡⟨ refl ⟩
       (M · M′) [ x ≔ N ]ₙ
     □
lemma-substnfv  {⟨ inj₂ (inj₂ (inj₁ (t , y , M))) ⟩}  {N} {x} x∉fv 
                (notOccurBR (notOccurBinj₂ (notOccurBinj₂  (notOccurBinj₁ (notOccurBx _ (notOccurBB≢ x≢y xnbM)))))) 
  =  begin≡
       ƛ y t M
     ≡⟨ cong (ƛ y t) (lemma-substnfv  {M}
                                      (lemma-∉  (sym≢ x≢y)
                                                (c∉xs++ys→c∉ys {x} {fvSF {tF} {|Ef| tyF} SortFTermVars t} x∉fv))
                                      xnbM)  ⟩  
       ƛ y t (M [ x ≔ N ]ₙ)
     ≡⟨ refl ⟩      
        (ƛ y t M) [ x ≔ N ]ₙ
     □
lemma-substnfv  {⟨ inj₂ (inj₂ (inj₂ (inj₁ (M , t)))) ⟩} {N} {x} x∉fv
                (notOccurBR (notOccurBinj₂ (notOccurBinj₂  (notOccurBinj₂ (notOccurBinj₁ (notOccurBx xnbM _))))))
  =  begin≡
        M ·ₜ t
      ≡⟨  cong (λ P →  P ·ₜ t) (lemma-substnfv {M} (c∉xs++ys→c∉xs x∉fv) xnbM) ⟩
        (M [ x ≔ N ]ₙ) ·ₜ t
      ≡⟨ refl ⟩
        (M ·ₜ t) [ x ≔ N ]ₙ
      □
lemma-substnfv  {⟨ inj₂ (inj₂ (inj₂ (inj₂ (α , M)))) ⟩} {N} {x} x∉fv
                (notOccurBR (notOccurBinj₂ (notOccurBinj₂  (notOccurBinj₂ (notOccurBinj₂ (notOccurBB≢ x≢α xnbM))))))
  =  begin≡
       Λ α M
     ≡⟨ cong (Λ α) (lemma-substnfv {M} x∉fv xnbM) ⟩
       Λ α (M [ x ≔ N ]ₙ)
     ≡⟨ refl ⟩
       (Λ α M) [ x ≔ N ]ₙ
     □
\end{code}

%<*substnaivecompositionpredicate>
\begin{code}
PSCn : {x y : V}{L : FTerm} → FTerm → FTerm → Set
PSCn {x} {y} {L} N M =  x ∉ y ∷ fv L →  x notOccurBind L
  →  (M [ x ≔ N ]ₙ) [ y ≔ L ]ₙ ∼α (M [ y ≔ L ]ₙ)[ x ≔ N [ y ≔ L ]ₙ ]ₙ
\end{code}
%</substnaivecompositionpredicate>

\begin{code}
lemma-substCompositionV  : {x y z : V}{N L : FTerm}
                         → x ∉ y ∷ fv  L
                         → x notOccurBind L
                         → (v z) [ x ≔ N ]ₙ [ y ≔ L ]ₙ ∼α (v z) [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ 
lemma-substCompositionV {x} {y} {z} {N} {L} x∉yfvL _ with x ≟v z
... | yes x≡z with y ≟v z 
...         | yes y≡z             = ⊥-elim ((b∉a∷xs→b≢a x∉yfvL) (trans x≡z (sym y≡z)))
...         | no  y≢z with x ≟v z
...                   |  yes _    = ρ
...                   |  no  x≢z  = ⊥-elim (x≢z x≡z)
lemma-substCompositionV {x} {y} {z} {N} {L} x∉yfvL xnbL
    | no  x≢z with y ≟v z 
...         | yes y≡z
  = subst  (λ M →  L ∼α M)
           (lemma-substnfv (lemma∉fvfvS {tF} {SortFTermVars} {L} (b∉a∷xs→b∉xs x∉yfvL)) xnbL) ρ 
...         | no  y≢z with x ≟v z
...                   |  yes x≡z  = ⊥-elim (x≢z x≡z)
...                   |  no  _    = ρ

-- Esto puede demostrarse genericamente usando fold fusion !
open ∼-Reasoning(tF)

\end{code}

%<*substcompositionNdef>
\begin{code}
lemma-substCompositionN :  {x y : V}{M N L : FTerm} → PSCn {x} {y} {L} N M
lemma-substCompositionN {x} {y} {M} {N} {L}
  = foldInd tF (PSCn {x} {y} {L} N) lemma-substCompositionNAux M
\end{code}
%</substcompositionNdef>

\begin{code}
  where
  lemma-substCompositionNAux : (e : ⟦ tF ⟧ (μ tF)) → fih tF (PSCn N) e → PSCn N ⟨ e ⟩  
  lemma-substCompositionNAux (inj₁ z) _ x∉yfvL xnbL = lemma-substCompositionV {x} {y} {z} {N} {L} x∉yfvL xnbL
  lemma-substCompositionNAux (inj₂ (inj₁ (M′  , M″ ))) (hiM′ , hiM″) x∉yfvL xnbL
    =   begin
          (M′ ·  M″ ) [ x ≔ N ]ₙ [ y ≔ L ]ₙ
        ≈⟨ refl ⟩
          ((M′ [ x ≔ N ]ₙ) ·  (M″ [ x ≔ N ]ₙ))  [ y ≔ L ]ₙ
        ≈⟨ refl ⟩
          (M′ [ x ≔ N ]ₙ [ y ≔ L ]ₙ) ·  (M″ [ x ≔ N ]ₙ [ y ≔ L ]ₙ)
        ∼⟨  ∼αR (∼α+₂ (∼α+₁ (∼αx (hiM′ x∉yfvL xnbL) (hiM″ x∉yfvL xnbL)))) ⟩
          (M′ [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ ) ·  (M″ [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ)
        ≈⟨ refl ⟩
          (M′ ·  M″) [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ 
        ∎
\end{code}

%<*substncompositionabstractioncase>
\begin{code}
  lemma-substCompositionNAux  (inj₂ (inj₂ (inj₁ (t , z , M))))
                              (_ , hiM) x∉yfvL x∉bL =  
    begin
      (ƛ z t M) [ x ≔ N ]ₙ [ y ≔ L ]ₙ
    ≈⟨ refl                                         ⟩
      ƛ z t (M [ x ≔ N ]ₙ [ y ≔ L ]ₙ)
    ∼⟨ ∼αR (∼α+₂  (∼α+₂ (∼α+₁
         (∼αx  ρF (lemma∼+B (hiM x∉yfvL x∉bL))))))  ⟩ 
      ƛ z t (M [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ)
    ≈⟨ refl                                         ⟩
      (ƛ z t M) [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ
    ∎
\end{code}
%</substncompositionabstractioncase>

\begin{code}
  lemma-substCompositionNAux (inj₂ (inj₂ (inj₂ (inj₁ (M , t))))) (hi , _) x∉yfvL xnbL
    =  begin
         (M ·ₜ t) [ x ≔ N ]ₙ [ y ≔ L ]ₙ
       ≈⟨ refl ⟩
         (M [ x ≔ N ]ₙ [ y ≔ L ]ₙ) ·ₜ t 
       ∼⟨ ∼αR (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₁ (∼αx (hi x∉yfvL xnbL) ρF))))) ⟩
         (M [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ) ·ₜ t 
       ≈⟨ refl ⟩
         (M ·ₜ t) [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ
       ∎
  lemma-substCompositionNAux (inj₂ (inj₂ (inj₂ (inj₂ (t , M))))) hi x∉yfvL xnbL
    =  begin
          (Λ t M) [ x ≔ N ]ₙ [ y ≔ L ]ₙ
       ≈⟨ refl ⟩
          Λ t (M [ x ≔ N ]ₙ [ y ≔ L ]ₙ)
       ∼⟨ ∼αR (∼α+₂ (∼α+₂ (∼α+₂ (∼α+₂ (∼αB [] (λ c c∉[] → lemma∼swapEquiv (hi x∉yfvL xnbL) t c)))))) ⟩
          Λ t (M [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ)
       ≈⟨ refl ⟩
          (Λ t M) [ y ≔ L ]ₙ [ x ≔ N [ y ≔ L ]ₙ ]ₙ
       ∎
\end{code}




Composition Lemma (exemplifies alpha induction principle usage)



--lemma-substComposition' :  {x y : V}{M N L : FTerm} → PSC {x} {y} {L} N M 
--lemma-substComposition' {x} {y} {M} {N} {L} p∉ = {!!}
\end{code}

%<*substcompositionpredicate>
\begin{code}
TreeFTermF =  |Ef| tF |x| |Ef| tF |x| |Ef| tF 
TreeFTerm = μ TreeFTermF

PSComp : {x y : V} → TreeFTerm → Set
PSComp {x} {y} ⟨ M , N , L ⟩ = x ∉ y ∷ fv L
    → (M [ x ≔ N ]) [ y ≔ L ] ∼α (M [ y ≔ L ])[ x ≔ N [ y ≔ L ] ]
\end{code}
%</substcompositionpredicate>


%<*substcompositionpredicatealpha>
\begin{code}
αCompatiblePSComp : ∀ {x y : V} → αCompatiblePred {TreeFTermF} (PSComp {x} {y})
αCompatiblePSComp  {x} {y} {⟨ M , N , L ⟩} {⟨ M′ , N′ , L′ ⟩} 
                   (∼αR (∼αx M∼M′ (∼αx N∼N′ L∼L′))) PMs x∉y:fvL′
  =  begin
       (M′  [ x ≔ N′  ])  [ y ≔ L′  ]
     -- Strong α compability of inner substitution operation       
     ≈⟨ cong (λ z → z [ y ≔ L′ ]) (lemma-substα (σ M∼M'))                                 ⟩
       (M   [ x ≔ N′  ])  [ y ≔ L′  ]
     -- Strong α compability of outter substitution operation       
     ≈⟨ lemma-substα  {M [ x ≔ N′ ]} {M [ x ≔ N ]} (lemma-substα′ {x} {M} (σ N∼N'))       ⟩
       (M   [ x ≔ N   ])  [ y ≔ L′  ]
     -- Outter substitution is alpha-compatible in its substituted argument
     ∼⟨ lemma-substα′ {y} {M [ x ≔ N   ]} (σ L∼L')                                        ⟩
       (M   [ x ≔ N   ])  [ y ≔ L   ]
     -- Application of the inductive hypothesis
     ∼⟨ PMs x∉y∶fvL                                                                       ⟩ 
       (M   [ y ≔ L   ])  [ x ≔ N   [ y ≔ L   ] ]
     -- Strong α compability of inner substitution operation       
     ≈⟨ cong  (λ P → P [ x ≔ N [ y ≔ L ] ]) (lemma-substα M∼M')                           ⟩ 
       (M′  [ y ≔ L   ])  [ x ≔ N   [ y ≔ L   ] ]
     -- Inner substitution is alpha-compatible in its substituted argument
     ≈⟨ lemma-substα   {M′ [ y ≔ L ]} {M′ [ y ≔ L′ ]} {N [ y ≔ L ]} {x}
                       (lemma-substα′ {y} {M′} L∼L')                                      ⟩        
       (M′  [ y ≔ L′  ])  [ x ≔ N   [ y ≔ L   ] ]
     -- Strong α compability of substitution operation in subsituted term       
     ≈⟨ cong  (λ P → (M′ [ y ≔ L′ ])  [ x ≔ P ]) (lemma-substα N∼N')                      ⟩
       (M′  [ y ≔ L′  ])  [ x ≔ N′  [ y ≔ L   ] ]
     -- Outter substitution is alpha-compatible in its substituted argument
     ∼⟨ lemma-substα′  {x} {M′  [ y ≔ L′ ]} {N′ [ y ≔ L ]} (lemma-substα′ {y} {N′} L∼L')  ⟩ 
       (M′  [ y ≔ L′  ])  [ x ≔ N′  [ y ≔ L′  ] ]
     ∎     
\end{code}
%</substcompositionpredicatealpha>

\begin{code}  
  where
  x∉y∶fvL : x ∉ y ∷ fv L
  x∉y∶fvL = subst (λ xs → x ∉ y ∷ xs) (lemma∼fv (σ (lemma-∼αEf L∼L′))) x∉y:fvL′
  M∼M' = lemma-∼αEf M∼M′
  N∼N' = lemma-∼αEf N∼N′
  L∼L' = lemma-∼αEf L∼L′
\end{code}


%<*substitutioncompositionproof>
\begin{code}
αproof :  {x y : V}(Ms : μ TreeFTermF)
  → ListNotOccurBind (x ∷ y ∷ []) Ms → ListNotOccurBind (fv Ms) Ms → PSComp {x} {y} Ms
αproof {x} {y} ⟨ M , N , L ⟩ nOcc nOcc2 x∉y∶fvL
   =  begin
         (M  [ x ≔ N  ])  [ y ≔ L ]
      ≈⟨ lemma-substα  {M [ x ≔ N ]} (lemmaSubsts {x} {M} {N} x:fvN∉bM)         ⟩
         M   [ x ≔ N ]ₙ   [ y ≔ L ]
      ∼⟨ lemmaSubsts {y} {M [ x ≔ N ]ₙ} {L} y:fvL∉bM[x≔N]ₙ                      ⟩
         M   [ x ≔ N ]ₙ   [ y ≔ L ]ₙ
      ∼⟨ lemma-substCompositionN  {x} {y} {M} {N} {L} x∉y∶fvL x∉bL              ⟩
         M   [ y ≔ L ]ₙ   [ x ≔ N [ y ≔ L ]ₙ  ]ₙ
      ∼⟨ lemma-substnα′  {x} {M [ y ≔ L ]ₙ} (σ (lemmaSubsts {y} {N} y:fvL∉bN))  ⟩
         M   [ y ≔ L ]ₙ   [ x ≔ N [ y ≔ L ]   ]ₙ
      ∼⟨ σ (lemmaSubsts  {x} {M [ y ≔ L ]ₙ} {N [ y ≔ L ]} x:fvN[y≔L]∉bM[y≔L]ₙ)  ⟩
         M   [ y ≔ L ]ₙ   [ x ≔ N [ y ≔ L ]   ]
      ≈⟨ lemma-substα (σ (lemmaSubsts {y} {M} {L} y:fvL∉bM))                    ⟩
         (M  [ y ≔ L  ])  [ x ≔ N [ y ≔ L ]   ]
       ∎
\end{code}
%</substitutioncompositionproof>

\begin{code}  
  where
  fvM++fvN++fvL∉bM,N,L : ListNotOccurBind {TreeFTermF} (fv M ++ fv N ++ fv L) ⟨ M , N , L ⟩
  fvM++fvN++fvL∉bM,N,L = subst (λ xs → ListNotOccurBind xs ⟨ M , N , L ⟩) (lemmafvtern {tF} {tF} {tF} {M} {N} {L}) nOcc2
  fvM++fvN++fvL∉bM : ListNotOccurBind (fv M ++ fv N ++ fv L) M
  fvM++fvN++fvL∉bM
    = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₁inv (lemmalistNotOccurBindFR→ListNotOccurBindF fvM++fvN++fvL∉bM,N,L))
  fvM++fvN++fvL∉bN : ListNotOccurBind (fv M ++ fv N ++ fv L) N
  fvM++fvN++fvL∉bN
    = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₁inv (listNotOccurBx₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF fvM++fvN++fvL∉bM,N,L)))
  fvM++fvN++fvL∉bL : ListNotOccurBind (fv M ++ fv N ++ fv L) L
  fvM++fvN++fvL∉bL
    = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₂inv (listNotOccurBx₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF fvM++fvN++fvL∉bM,N,L)))
  x:y∉bM : ListNotOccurBind (x ∷ y ∷ []) M
  x:y∉bM = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₁inv (lemmalistNotOccurBindFR→ListNotOccurBindF nOcc))
  x:y∉bN : ListNotOccurBind (x ∷ y ∷ []) N
  x:y∉bN = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₁inv (listNotOccurBx₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nOcc)))
  x:y∉bL : ListNotOccurBind (x ∷ y ∷ []) L
  x:y∉bL = lemmalistNotOccurBindEf→ListNotOccurBindR (listNotOccurBx₂inv (listNotOccurBx₂inv (lemmalistNotOccurBindFR→ListNotOccurBindF nOcc)))
  x:fvN∉bM : ListNotOccurBind (x ∷ fv  N) M
  x:fvN∉bM = lemma-binds:cons (lemma-binds:head x:y∉bM) (lemma-binds++l (lemma-binds++r {fv M} fvM++fvN++fvL∉bM))
  x∉bL : x notOccurBind L
  x∉bL = lemma-binds:head x:y∉bL
  y:fvL∉bM : ListNotOccurBind (y ∷ fv L) M
  y:fvL∉bM = lemma-binds:cons (lemma-binds:head (lemma-binds:tail x:y∉bM)) (lemma-binds++r {fv N} (lemma-binds++r {fv M} fvM++fvN++fvL∉bM))
  y:fvL∉bN : ListNotOccurBind (y ∷ fv L) N
  y:fvL∉bN = lemma-binds:cons (lemma-binds:head (lemma-binds:tail x:y∉bN)) (lemma-binds++r {fv N} (lemma-binds++r {fv M} fvM++fvN++fvL∉bN))
  y:fvL∉bM[x≔N]ₙ : ListNotOccurBind (y ∷ fv L) (M [ x ≔ N ]ₙ)
  y:fvL∉bM[x≔N]ₙ
    = lemma-foldCtxBinds {cF} {tF} {tF} {substaux} (lemma-substauxBinds (lemma-binds:cons (notOccurBR (notOccurBx notOccurBv (notOccurBindR→notOccurBindEf (lemma-binds:head y:fvL∉bN)))) (lemma-bindsR (lemma-binds× lemma-bindsv (lemmalistNotOccurBindFR→ListNotOccurBindEf (lemma-binds:tail y:fvL∉bN)))))) y:fvL∉bM 
  [x]∉bM[y≔L]ₙ : ListNotOccurBind (x ∷ []) (M [ y ≔ L ]ₙ)
  [x]∉bM[y≔L]ₙ = lemma-foldCtxBinds {cF} {tF} {tF} {substaux} (lemma-substauxBinds (lemma-bindsR ( lemma-binds× (notOccurBv ∷ []) ( lemmalistNotOccurBindFR→ListNotOccurBindEf ( lemma-binds:cons  (lemma-binds:head x:y∉bL) []))))) (lemma-binds:cons (lemma-binds:head x:y∉bM ) [])
  fv⟨y,L⟩∉bM : {L : μ tF} → ListNotOccurBind (y ∷ fv L) M → ListNotOccurBind (fv {cF} ⟨ y , L ⟩) M
  fv⟨y,L⟩∉bM {⟨ L ⟩} y:fvL∉bM = lemma-binds:cons (lemma-binds:head y:fvL∉bM) (lemma-binds:tail y:fvL∉bM)
  y∉bL : y notOccurBind L
  y∉bL = lemma-binds:head (lemma-binds:tail x:y∉bL)
  fvL∉bL : ListNotOccurBind (fv L) L
  fvL∉bL = lemma-binds++r {fv N} (lemma-binds++r {fv M} fvM++fvN++fvL∉bL)
  fv⟨y,L⟩∉b⟨y,L⟩ : {L : μ tF} → y notOccurBind L → ListNotOccurBind (fv L) L → ListNotOccurBind (fv {cF}⟨ y , L ⟩) ⟨ y , L ⟩
  fv⟨y,L⟩∉b⟨y,L⟩ {⟨ L ⟩} y∉bL fvL∉bL = lemma-binds:cons (notOccurBR (notOccurBx notOccurBv (notOccurBEf (notOccurBRinv y∉bL)))) ((lemma-bindsR (lemma-binds× lemma-bindsv (lemmalistNotOccurBindFR→ListNotOccurBindEf fvL∉bL))))
  fvN[y≔L]ₙ∉bM[y≔L]ₙ : ListNotOccurBind (fv (N [ y ≔ L ]ₙ)) (M [ y ≔ L ]ₙ)
  fvN[y≔L]ₙ∉bM[y≔L]ₙ
    = lemma-binds⊆  {fv {cF} ⟨ y , L ⟩ ++ fv N} {fv (N [ y ≔ L ]ₙ)}
                    (foldCtxFV {cF} {tF} {tF} {⟨ y , L ⟩} {N} {substaux}) 
                    (lemma-binds++  {fv {cF} ⟨ y , L ⟩} {fv N}
                                    (lemma-foldCtxBinds  {cF} {tF} {tF} {substaux} {⟨ y , L ⟩} {M} {fv {cF} ⟨ y , L ⟩} (lemma-substauxBinds (fv⟨y,L⟩∉b⟨y,L⟩ {L} y∉bL fvL∉bL)) (fv⟨y,L⟩∉bM {L} y:fvL∉bM))
                                    (lemma-foldCtxBinds  {cF} {tF} {tF} {substaux}
                                                         (lemma-substauxBinds (lemma-bindsR ( lemma-binds× lemma-bindsv (lemmalistNotOccurBindFR→ListNotOccurBindEf (lemma-binds++l (lemma-binds++r {fv M} fvM++fvN++fvL∉bL))))))
                                                         (lemma-binds++l (lemma-binds++r {fv M} fvM++fvN++fvL∉bM))))
  x:fvN[y≔L]ₙ∉bM[y≔L]ₙ : ListNotOccurBind (x ∷ fv (N [ y ≔ L ]ₙ)) (M [ y ≔ L ]ₙ)
  x:fvN[y≔L]ₙ∉bM[y≔L]ₙ = lemma-binds:cons (lemma-binds:head [x]∉bM[y≔L]ₙ) fvN[y≔L]ₙ∉bM[y≔L]ₙ
  x:fvN[y≔L]∉bM[y≔L]ₙ : ListNotOccurBind (x ∷ fv (N [ y ≔ L ])) (M [ y ≔ L ]ₙ)
  x:fvN[y≔L]∉bM[y≔L]ₙ = subst (λ xs → ListNotOccurBind (x ∷ xs) (M [ y ≔ L ]ₙ)) (lemma∼fv (σ (lemmaSubsts y:fvL∉bN))) x:fvN[y≔L]ₙ∉bM[y≔L]ₙ
\end{code}

%<*substcompalphaproof>
\begin{code}
lemma-substComposition2  :  {x y : V}{Ms : TreeFTerm} → PSComp {x} {y} Ms
lemma-substComposition2 {x} {y} {⟨ M , N , L ⟩}
 = αProof  (PSComp {x} {y}) (x ∷ y ∷ []) 
           (αCompatiblePSComp {x} {y})
           αproof
           ⟨ M , N , L ⟩
\end{code}
%</substcompalphaproof>



Parallel Reduction

\begin{code}
open import Relation.Relation FTerm 
infix 7 _⇉n_
\end{code}

\begin{code}
data _⇉n_ : Rel where
  ⇉nv  :  {x : V}
         → v x ⇉n v x
  ⇉nƛ  :  {M N : FTerm}{x : V}{t : FType}
         → M ⇉n N
         → ƛ x t M ⇉n ƛ x t N
  ⇉n·  :  {M M' N N' : FTerm}
         → M ⇉n M' → N ⇉n N'
         → M · N ⇉n M' · N'
  ⇉n·ₜ :  {M N : FTerm}{t : FType}
         → M ⇉n N
         → M ·ₜ t ⇉n N ·ₜ t
  ⇉nΛ  :  {M N : FTerm}{α : V}
         → M ⇉n N
         → Λ α M ⇉n Λ α N
  ⇉nβ :   {M M' N N' P : FTerm}{t : FType}{x : V}
         → M ⇉n M' 
         → N ⇉n N'
         → ƛ x t M · N ⇉n M' [ x ≔ N' ]ₙ
\end{code}

All lemmas about ⇉n relation must have freshness premises so naive substitution behaves correctly

-- \begin{code}
-- FourFTermF =  |Ef| tF |x| |Ef| tF |x| |Ef| tF |x| |Ef| tF 
-- FourFTerm = μ FourFTermF

-- lemma-⇉SubstN :  {x : V}{M M' N N' : FTerm }
--                  → ListNotOccurBind {FourFTermF}
--                       (x ∷ fv {FourFTermF} ⟨ M , M' , N , N' ⟩)
--                       ⟨ M , M' , N , N' ⟩
--                  → M ⇉n M' → N ⇉n N'
--                  → M [ x ≔ N ]ₙ ⇉n M' [ x ≔ N' ]ₙ
-- lemma-⇉SubstN = {!!}

-- diam⇉n :  {M N P : FTerm} → ListNotOccurBind (fv M) M
--           → M ⇉n N → M ⇉n P → ∃ (λ R → N ⇉n R × P ⇉n R)
-- diam⇉n = {!!}
-- \end{code}

-- \begin{code}
-- infix 7 _⇉_

-- bvcFTerm : FTerm → FTerm
-- bvcFTerm M = proj₁ (bindersFreeαElem (fv M) M)

-- _⇉_ : Rel
-- M ⇉ N = ∃ (λ N' → M' ⇉n N' × N' ∼α N)
--   where
--   M' = bvcFTerm M

-- lemma-⇉rightα : {M N P : FTerm} → M ⇉ N → N ∼α P → M ⇉ P
-- lemma-⇉rightα {P = P} (N' , M'⇉N' , N'∼N) N∼P =  N' , M'⇉N' , τ N'∼N N∼P

-- lemma-⇉leftα : {M N P : FTerm} → P ∼α M → M ⇉ N → P ⇉ N
-- lemma-⇉leftα {M} {N} {P} P∼M M⇉N
--   with bvcFTerm P | bvcFTerm M | lemma-bindersFreeαFV P∼M
-- ... | M' | .M' | refl  = M⇉N
-- \end{code}


-- \begin{code}
-- ρ⇉ : Reflexive (_⇉_)
-- ρ⇉ = {!!}

-- τ⇉ : Transitive (_⇉_)
-- τ⇉ = {!!} 

-- module ⇉-Reasoning where
--   ⇉-preorder : Preorder _ _ _
--   ⇉-preorder =  
--              record { 
--              Carrier = FTerm;
--              _≈_ = _≡_;
--              _∼_ = _⇉_;
--              isPreorder =  record {
--              isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid FTerm) ;
--              reflexive = λ { {M} {.M} refl → ρ⇉};
--              trans = τ⇉ } }

--   import Relation.Binary.PreorderReasoning as PreR⇉
--   open PreR⇉ ⇉-preorder renaming (begin_ to begin⇉_;_∼⟨_⟩_ to _⇉⟨_⟩_;_≈⟨_⟩_ to _⇉≈⟨_⟩_;_∎ to _∎⇉) public
-- \end{code}

-- Ctx can be done generically

-- \begin{code}
-- data ctx (r : Rel) : Rel where
--   ctxinj : ∀ {t t'}       → r t t'        → ctx r t t'
--   ctx·l  : ∀ {t₁ t₁' t₂}  → ctx r t₁ t₁'  → ctx r (t₁ · t₂)   (t₁' · t₂)
--   ctx·r  : ∀ {t₁ t₂ t₂'}  → ctx r t₂ t₂'  → ctx r (t₁ · t₂)   (t₁ · t₂')
--   ctx·ₜ  : ∀ {t₁ t₁' t₂}  → ctx r t₁ t₁'  → ctx r (t₁ ·ₜ t₂)  (t₁' ·ₜ t₂)
--   ctxƛ   : ∀ {x t t₁ t₁'} → ctx r t₁ t₁'  → ctx r (ƛ x t t₁)  (ƛ x t t₁')
--   ctxΛ   : ∀ {t t₁ t₁'}   → ctx r t₁ t₁'  → ctx r (Λ t t₁)    (Λ t t₁')

-- infix 1 _▹_ 
-- data _▹_ : Rel where
--   ▹β  :  {M N : FTerm}{x : V}{t : FType} 
--       →  ƛ x t M · N ▹ M [ x ≔ N ]

-- infix 4 _→β_
-- _→β_ : Rel
-- _→β_ = ctx _▹_

-- infix 4 _→α_ 
-- _→α_ : Rel
-- _→α_ = _→β_ ∪ _∼α_

-- infix 4 _→α*_
-- _→α*_ : Rel
-- _→α*_ = star _→α_
-- \end{code}

-- \begin{code}

-- -- This 3 results are what I need !

-- lemma→α⊆⇉ : _→α_ ⊆ _⇉_
-- lemma→α⊆⇉ (inj₁ (ctxinj (▹β {M}))) = {! ⇉β ρ⇉ ρ⇉!}
-- lemma→α⊆⇉ (inj₁ (ctx·l x))   = {!!}
-- lemma→α⊆⇉ (inj₁ (ctx·r x))   = {!!}
-- lemma→α⊆⇉ (inj₁ (ctx·ₜ x))   = {!!}
-- lemma→α⊆⇉ (inj₁ (ctxƛ x₁))   = {!!}
-- lemma→α⊆⇉ (inj₁ (ctxΛ x))    = {!!}
-- lemma→α⊆⇉ (inj₂ (∼αR y))     = {!!}

-- lemma⇉⊆→α* : _⇉_ ⊆ _→α*_
-- lemma⇉⊆→α* = {!!}

-- diam⇉ : diamond _⇉_
-- diam⇉ = {!!}

-- lemma-CR⇉ : cr _⇉_
-- lemma-CR⇉ = diamond-cr diam⇉
-- --
-- lemma-CR→α : cr _→α_
-- lemma-CR→α = cr-⊆ lemma→α⊆⇉ lemma⇉⊆→α* lemma-CR⇉
-- \end{code}




-- \begin{code}
-- open ⇉-Reasoning

-- Psubst⇉ : {N N' : FTerm}(x : V) → FTerm → Set
-- Psubst⇉ {N} {N'} x M = {M' : FTerm} → M ⇉ M' → N ⇉ N' → M [ x ≔ N ] ⇉ M' [ x ≔ N' ]

-- αCompP⇉[] : {N N' : FTerm}(x : V) → αCompatiblePred (Psubst⇉ {N} {N'} x)
-- αCompP⇉[] {N} {N'} x {M} {P} M∼P P⇉[]M {M'} P⇉M' N⇉N' 
--   =  begin⇉
--        P [ x ≔ N ]
--      ⇉⟨ {!!} ⟩
--        M' [ x ≔ N' ]
--      ∎⇉

-- lemma⇉Subst : {N N' : FTerm}(x : V)(M : FTerm) → Psubst⇉ {N} {N'} x M
-- lemma⇉Subst {N} {N'} x M = {!!}
-- \end{code}

-- \begin{code}
-- RelF : Functor
-- RelF = tF |x| tF
-- \end{code}


