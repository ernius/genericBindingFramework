Swap

\begin{code}
module Swap where

open import Atom
open import GPBindings 
open import Nat.NatProperties

open import Function
open import Data.Nat hiding (fold)
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _■)
\end{code}

%<*swapF>
\begin{code}
swapF  :  {F : Functor}(G : Functor) → Sort → V → V → ⟦ G ⟧ (μ F) → ⟦ G ⟧ (μ F)
swapF |1|           S a b tt         =  tt
swapF {F} |R|       S a b ⟨ e ⟩      =  ⟨ swapF F S a b e ⟩
swapF (|E|    _)    S a b e          =  e
swapF (|Ef|   G)    S a b ⟨ e ⟩      =  ⟨ swapF G S a b e ⟩
swapF (G₁ |+|  G₂)  S a b (inj₁ e)   =  inj₁ (swapF G₁ S a b e)
swapF (G₁ |+|  G₂)  S a b (inj₂ e)   =  inj₂ (swapF G₂ S a b e)
swapF (G₁ |x|  G₂)  S a b (e₁ , e₂)  =  swapF G₁ S a b e₁  , swapF G₂ S a b e₂
swapF (|v|    S')   S a b c with S' ≟S S
... | yes  _                         =  （ a ∙ b ）ₐ c
... | no   _                         =  c
swapF (|B| S'  G)   S a b (c , e) with S' ≟S S
... | yes  _                        =   （ a ∙ b ）ₐ   c     , swapF G S a b e
... | no   _                        =   c                  , swapF G S a b e
\end{code}
%</swapF>

%<*swap>
\begin{code}
swap : {F : Functor} → Sort → V → V → μ F → μ F
swap S a b e = swapF |R| S a b e
\end{code}
%</swap>

\begin{code}
lemmaSwapId : {F G : Functor}{S : Sort}{a : V}{e : ⟦ G ⟧ (μ F)} → e ≡ swapF G S a a e
lemmaSwapId {F} {|1|}       {S} {a} {e}       = refl
lemmaSwapId {F} {|R|}       {S} {a} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapId {F} {F} {S} {a} {e})
lemmaSwapId {F} {|E| x}     {S} {a} {e}       = refl
lemmaSwapId {F} {|Ef| G}    {S} {a} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapId {G} {G} {S} {a} {e})
lemmaSwapId {F} {G₁ |+| G₂} {S} {a} {inj₁ e}  = cong inj₁ (lemmaSwapId {F} {G₁} {S} {a} {e})
lemmaSwapId {F} {G₁ |+| G₂} {S} {a} {inj₂ e}  = cong inj₂ (lemmaSwapId {F} {G₂} {S} {a} {e})
lemmaSwapId {F} {G₁ |x| G₂} {S} {a} {e , e'}  = cong₂ (_,_) (lemmaSwapId {F} {G₁} {S} {a} {e}) (lemmaSwapId {F} {G₂} {S} {a} {e'}) 
lemmaSwapId {F} {|v| S'}    {S} {a} {e}       with S' ≟v S
... | yes _                                   = sym lemma（aa）b≡b
... | no  _                                   = refl
lemmaSwapId {F} {|B| S' G}  {S} {a} {x , e}   with S' ≟v S
... | yes _                                   = cong₂ (_,_) (sym lemma（aa）b≡b)  (lemmaSwapId {F} {G} {S} {a} {e}) 
... | no  _                                   = cong₂ (_,_) refl (lemmaSwapId {F} {G} {S} {a} {e}) 
\end{code}

\begin{code}
lemmaSwapIdem : {F G : Functor}{S : Sort}{a b : V}{e : ⟦ G ⟧ (μ F)} → e ≡ swapF G S a b (swapF G S a b e)
lemmaSwapIdem {F} {|1|}       {S} {a} {b} {e}       = refl
lemmaSwapIdem {F} {|R|}       {S} {a} {b} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapIdem {F} {F} {S} {a} {b} {e})
lemmaSwapIdem {F} {|E| x}     {S} {a} {b} {e}       = refl
lemmaSwapIdem {F} {|Ef| G}    {S} {a} {b} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapIdem {G} {G} {S} {a} {b} {e})
lemmaSwapIdem {F} {G₁ |+| G₂} {S} {a} {b} {inj₁ e}  = cong inj₁ (lemmaSwapIdem {F} {G₁} {S} {a} {b} {e})
lemmaSwapIdem {F} {G₁ |+| G₂} {S} {a} {b} {inj₂ e}  = cong inj₂ (lemmaSwapIdem {F} {G₂} {S} {a} {b} {e})
lemmaSwapIdem {F} {G₁ |x| G₂} {S} {a} {b} {e , e'}  = cong₂ (_,_) (lemmaSwapIdem {F} {G₁} {S} {a} {b} {e}) (lemmaSwapIdem {F} {G₂} {S} {a} {b} {e'}) 
lemmaSwapIdem {F} {|v| S'}    {S} {a} {b} {e}       with S' ≟v S
... | yes _                                   = sym lemma（ab）（ab）c≡c
... | no  _                                   = refl
lemmaSwapIdem {F} {|B| S' G}  {S} {a} {b} {x , e}   with S' ≟v S
... | yes _                                   = cong₂ (_,_) (sym lemma（ab）（ab）c≡c) (lemmaSwapIdem {F} {G} {S} {a} {b} {e}) 
... | no  _                                   = cong₂ (_,_) refl (lemmaSwapIdem {F} {G} {S} {a} {b} {e}) 
\end{code}

\begin{code}
lemmaSwapComm : {F G : Functor}{S : Sort}{a b : V}{e : ⟦ G ⟧ (μ F)} → swapF G S a b e ≡ swapF G S b a e
lemmaSwapComm {F} {|1|}       {S} {a} {b} {e}       = refl
lemmaSwapComm {F} {|R|}       {S} {a} {b} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapComm {F} {F} {S} {a} {b} {e})
lemmaSwapComm {F} {|E| x}     {S} {a} {b} {e}       = refl
lemmaSwapComm {F} {|Ef| G}    {S} {a} {b} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapComm {G} {G} {S} {a} {b} {e})
lemmaSwapComm {F} {G₁ |+| G₂} {S} {a} {b} {inj₁ e}  = cong inj₁ (lemmaSwapComm {F} {G₁} {S} {a} {b} {e})
lemmaSwapComm {F} {G₁ |+| G₂} {S} {a} {b} {inj₂ e}  = cong inj₂ (lemmaSwapComm {F} {G₂} {S} {a} {b} {e})
lemmaSwapComm {F} {G₁ |x| G₂} {S} {a} {b} {e , e'}  = cong₂ (_,_) (lemmaSwapComm {F} {G₁} {S} {a} {b} {e}) (lemmaSwapComm {F} {G₂} {S} {a} {b} {e'}) 
lemmaSwapComm {F} {|v| S'}    {S} {a} {b} {c}       with S' ≟v S
... | yes _                                   = lemma∙ₐcomm {a} {b} {c}
... | no  _                                   = refl
lemmaSwapComm {F} {|B| S' G}  {S} {a} {b} {c , e}   with S' ≟v S
... | yes _                                   = cong₂ (_,_) (lemma∙ₐcomm {a} {b} {c}) (lemmaSwapComm {F} {G} {S} {a} {b} {e}) 
... | no  _                                   = cong₂ (_,_) refl (lemmaSwapComm {F} {G} {S} {a} {b} {e}) 
\end{code}

\begin{code}
lemmaSwapIdemComm : {F G : Functor}{S : Sort}{a b : V}{e : ⟦ G ⟧ (μ F)} → e ≡ swapF G S b a (swapF G S a b e)
lemmaSwapIdemComm {F} {G} {S} {a} {b} {e} = sym (begin≡
  swapF G S b a (swapF G S a b e)
    ≡⟨ lemmaSwapComm {F} {G} {S} {b} {a} {(swapF G S a b e)} ⟩
  swapF G S a b (swapF G S a b e)
    ≡⟨ sym (lemmaSwapIdem {F} {G} {S} {a} {b} {e}) ⟩  
    e
  ■)
\end{code}

\begin{code}
lemmaSwapDistributiveF : {F G : Functor}{S : Sort}{a b c d : V}{e : ⟦ G ⟧ (μ F)}
 → swapF G S a b (swapF G S c d e) ≡ swapF G S (（ a ∙ b ）ₐ c) (（ a ∙ b ）ₐ d) (swapF G S a b e)
lemmaSwapDistributiveF {F} {|1|}       {S} {a} {b} {c} {d} {e}       = refl
lemmaSwapDistributiveF {F} {|R|}       {S} {a} {b} {c} {d} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapDistributiveF {F} {F} {S} {a} {b} {c} {d} {e})
lemmaSwapDistributiveF {F} {|E| x}     {S} {a} {b} {c} {d} {e}       = refl
lemmaSwapDistributiveF {F} {|Ef| G}    {S} {a} {b} {c} {d} {⟨ e ⟩}   = cong (⟨_⟩) (lemmaSwapDistributiveF {G} {G} {S} {a} {b} {c} {d} {e})
lemmaSwapDistributiveF {F} {G₁ |+| G₂} {S} {a} {b} {c} {d} {inj₁ e}  = cong inj₁ (lemmaSwapDistributiveF {F} {G₁} {S} {a} {b} {c} {d} {e})
lemmaSwapDistributiveF {F} {G₁ |+| G₂} {S} {a} {b} {c} {d} {inj₂ e}  = cong inj₂ (lemmaSwapDistributiveF {F} {G₂} {S} {a} {b} {c} {d} {e})
lemmaSwapDistributiveF {F} {G₁ |x| G₂} {S} {a} {b} {c} {d} {e , e'}  = cong₂ (_,_) (lemmaSwapDistributiveF {F} {G₁} {S} {a} {b} {c} {d} {e}) (lemmaSwapDistributiveF {F} {G₂} {S} {a} {b} {c} {d} {e'}) 
lemmaSwapDistributiveF {F} {|v| S'}    {S} {a} {b} {c} {d} {e}       with S' ≟v S
... | yes _                                   = lemma∙ₐdistributive a b c d e
... | no  _                                   = refl
lemmaSwapDistributiveF {F} {|B| S' G}  {S} {a} {b} {c} {d} {x , e}   with S' ≟v S
... | yes _                                   = cong₂ (_,_) (lemma∙ₐdistributive a b c d x) (lemmaSwapDistributiveF {F} {G} {S} {a} {b} {c} {d} {e}) 
... | no  _                                   = cong₂ (_,_) refl (lemmaSwapDistributiveF {F} {G} {S} {a} {b} {c} {d} {e}) 
\end{code}

\begin{code}
lemmaSwapDistributiveF≢ : {F G : Functor}{S S' : Sort}{a b c d : V}{e : ⟦ G ⟧ (μ F)} → S ≢ S'
                      → swapF G S' a b (swapF G S c d e) ≡ swapF G S c d (swapF G S' a b e)
lemmaSwapDistributiveF≢ {F} {|1|}       {S} {S'} {a} {b} {c} {d} {e}      S≢S' = refl
lemmaSwapDistributiveF≢ {F} {|R|}       {S} {S'} {a} {b} {c} {d} {⟨ e ⟩}  S≢S' = cong (⟨_⟩) (lemmaSwapDistributiveF≢ {F} {F} {S} {S'} {a} {b} {c} {d} {e} S≢S')
lemmaSwapDistributiveF≢ {F} {|E| x}     {S} {S'} {a} {b} {c} {d} {e}      S≢S' = refl
lemmaSwapDistributiveF≢ {F} {|Ef| G}    {S} {S'} {a} {b} {c} {d} {⟨ e ⟩}  S≢S' = cong (⟨_⟩) (lemmaSwapDistributiveF≢ {G} {G} {S} {S'} {a} {b} {c} {d} {e} S≢S')
lemmaSwapDistributiveF≢ {F} {G₁ |+| G₂} {S} {S'} {a} {b} {c} {d} {inj₁ e} S≢S' = cong inj₁ (lemmaSwapDistributiveF≢ {F} {G₁} {S} {S'} {a} {b} {c} {d} {e} S≢S')
lemmaSwapDistributiveF≢ {F} {G₁ |+| G₂} {S} {S'} {a} {b} {c} {d} {inj₂ e} S≢S' = cong inj₂ (lemmaSwapDistributiveF≢ {F} {G₂} {S} {S'} {a} {b} {c} {d} {e} S≢S')
lemmaSwapDistributiveF≢ {F} {G₁ |x| G₂} {S} {S'} {a} {b} {c} {d} {e , e'} S≢S' = cong₂ (_,_) (lemmaSwapDistributiveF≢ {F} {G₁} {S} {S'} {a} {b} {c} {d} {e} S≢S') (lemmaSwapDistributiveF≢ {F} {G₂} {S} {S'} {a} {b} {c} {d} {e'} S≢S') 
lemmaSwapDistributiveF≢ {F} {|v| S''}    {S} {S'} {a} {b} {c} {d} {e}      S≢S' with S'' ≟v S'
... | yes S''≡S' with S'' ≟v S
...      | yes S''≡S = ⊥-elim (S≢S' (trans (sym S''≡S) S''≡S'))
...      | no  S''≢S = refl
lemmaSwapDistributiveF≢ {F} {|v| S''}    {S} {S'} {a} {b} {c} {d} {e}      S≢S'
    | no  S''≢S' with S'' ≟v S
...      | yes S''≡S = refl 
...      | no  S''≢S = refl
lemmaSwapDistributiveF≢ {F} {|B| S'' G}  {S} {S'} {a} {b} {c} {d} {x , e}  S≢S' with S'' ≟v S'
... | yes S''≡S' with S'' ≟v S
...      | yes S''≡S = ⊥-elim (S≢S' (trans (sym S''≡S) S''≡S')) 
...      | no  S''≢S = cong₂ (_,_) refl (lemmaSwapDistributiveF≢ {F} {G} {S} {S'}  {a} {b} {c} {d} {e} S≢S')
lemmaSwapDistributiveF≢ {F} {|B| S'' G}  {S} {S'} {a} {b} {c} {d} {x , e}  S≢S'
    | no  S''≢S' with S'' ≟v S
...      | yes S''≡S = cong₂ (_,_) refl (lemmaSwapDistributiveF≢ {F} {G} {S} {S'}  {a} {b} {c} {d} {e} S≢S') 
...      | no  S''≢S = cong₂ (_,_) refl (lemmaSwapDistributiveF≢ {F} {G} {S} {S'}  {a} {b} {c} {d} {e} S≢S')
\end{code}

-- swap : (F : Functor) → Sort → V → V → μ F → μ F
-- swap F S a b = fold F (⟨_⟩ ∘ swapaux {F} F)
--   where
--   swapaux : {F : Functor}(G : Functor) → ⟦ G ⟧ (μ F) → ⟦ G ⟧ (μ F)
--   swapaux (|v| S')   c
--     with  S' ≟S S
--   ... | yes _                 = （ a ∙ b ）ₐ c
--   ... | no  _                 = c 
--   swapaux |1|        e        = e
--   swapaux (|E| A)    e        = e
--   swapaux (|Ef| G)   e        = e
--   swapaux |R|        e        = e
--   swapaux (G |+| G₁) e        = e
--   swapaux (G |x| G₁) e        =  e
--   swapaux (|B| S' G) (x , e)
--     with S' ≟v S
--   ... | yes _                 = （ a ∙ b ）ₐ  x , e
--   ... | no  _                 =              x , e

\begin{code}
lemmaSwapSize :  (F G : Functor)(S : Sort)(x y : V)(e : ⟦ G ⟧ (μ F)) 
                 → sizeF G (swapF G S x y e) ≡ sizeF G e
lemmaSwapSize F (|v| S')    S x y e         = refl
lemmaSwapSize F |1|         S x y e         = refl
lemmaSwapSize F |R|         S x y ⟨ e ⟩     = lemmaSwapSize F F S x y e
lemmaSwapSize F (|E| A)     S x y e         = refl
lemmaSwapSize F (|Ef| G)    S x y ⟨ e ⟩     = lemmaSwapSize G G S x y e
lemmaSwapSize F (G |+| G₁)  S x y (inj₁ e)  = lemmaSwapSize F G S x y e
lemmaSwapSize F (G |+| G₁)  S x y (inj₂ e)  = lemmaSwapSize F G₁ S x y e
lemmaSwapSize F (G |x| G₁)  S x y (e , e')  = cong₂ _+_ (lemmaSwapSize F G S x y e) (lemmaSwapSize F G₁ S x y e')
lemmaSwapSize F (|B| S' G)  S x y (z , e)  with S' ≟v S 
... | yes _  = cong suc (lemmaSwapSize F G S x y e)
... | no _   = cong suc (lemmaSwapSize F G S x y e)

mutual
  data AccF (F : Functor) : (G : Functor) → ⟦ G ⟧ (μ F) → Set where
    accv   :  {a : V}{S : Sort}                 →  AccF F (|v| S)      a
    acc1   :                                       AccF F |1|          tt
    accE   :  {A : Set}{a : A}                  →  AccF F (|E| A)      a
    accEf  :  {H : Functor}{e : μ H} 
              → Accμ e                          →  AccF F (|Ef| H)     e
    accR   :  {e : μ F} → Accμ e                →  AccF F |R|          e
    acc+₁  :  {G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}
              →  AccF F G₁ e                    →  AccF F (G₁ |+| G₂)  (inj₁ e)
    acc+₂  :  {G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)}
              →  AccF F G₂ e                    →  AccF F (G₁ |+| G₂)  (inj₂ e)
    accx  :  {G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)}
             →  AccF F G₁ e₁ → AccF F G₂ e₂     →  AccF F (G₁ |x| G₂)  (e₁ , e₂)
    accB  :  {G : Functor}{x : V}{S : Sort}{e : ⟦ G ⟧ (μ F)}
             →  ((y : V) → AccF F G (swapF G S x y e))
                                                →  AccF F (|B| S G)    (x , e)

  Accμ : {F : Functor} → μ F → Set
  Accμ {F} ⟨ e ⟩ = AccF F F e

open import Induction.WellFounded

accFNat : {F G : Functor}(e : ⟦ G ⟧ (μ F))(n : ℕ) → Acc _<′_ n → sizeF G e ≡ n → AccF F G e
accFNat {G = |v| x}      e         n accn |e|≡n = accv
accFNat {G = |1|}        e         n accn |e|≡n = acc1
accFNat {F} {|R|}        ⟨ e ⟩     n accn |e|≡n = accR   (accFNat {F} {F} e n accn |e|≡n)
accFNat {G = |E| x}      e         n accn |e|≡n = accE
accFNat {G = |Ef| G}     ⟨ e ⟩     n accn |e|≡n = accEf  (accFNat {G} {G} e n accn |e|≡n)
accFNat {G = G₁ |+| G₂}  (inj₁ e)  n accn |e|≡n = acc+₁  (accFNat {G = G₁} e n accn |e|≡n)
accFNat {G = G₁ |+| G₂}  (inj₂ e)  n accn |e|≡n = acc+₂  (accFNat {G = G₂} e n accn |e|≡n)
accFNat {G = G₁ |x| G₂}  (e₁ , e₂) .(sizeF G₁ e₁ + sizeF G₂ e₂ )  (acc f) refl 
  = accx  (accFNat {G = G₁} e₁ (sizeF G₁ e₁) (f (sizeF G₁ e₁) (lemman>0→m+1≤m+n (lemmasizeF>0 {G = G₂} e₂))) refl) 
          (accFNat {G = G₂} e₂ (sizeF G₂ e₂) (f (sizeF G₂ e₂) (lemmam>0→n+1≤m+n (lemmasizeF>0 {G = G₁} e₁))) refl)
accFNat {F} {|B| S G}    (x  , e)  .(suc (sizeF G e))             (acc f) refl 
  = accB (λ y → accFNat (swapF G S x y e) (sizeF G e) (f (sizeF G e) ≤′-refl) (lemmaSwapSize F G S x y e))

open import Induction.Nat

accF : {F : Functor}(e : μ F) → AccF F |R| e
accF {F} e = accFNat e (size e) (Induction.Nat.<-well-founded (size e)) refl

lemmaSwapFoldEquivF : {F G H : Functor}{S : Sort}{x y : V}{e : ⟦ G ⟧ (μ F)}
     {f  : ⟦ F ⟧ (μ H) → μ H}
  →  ({x y : V}{e  : ⟦ F ⟧ (μ H)} → f (swapF F S x y e) ≡ swap {H} S x y (f e))
  →  foldmap F G f (swapF G S x y e) ≡ swapF G S x y (foldmap F G f e)
lemmaSwapFoldEquivF      {G = |v| x}                     prf = refl
lemmaSwapFoldEquivF      {G = |1|}                       prf = refl
lemmaSwapFoldEquivF {F}  {|R|}          {e = ⟨ e ⟩} {f}  prf 
  = trans (cong f (lemmaSwapFoldEquivF {F} {F} prf)) prf
lemmaSwapFoldEquivF      {G = |E|   _}                   prf = refl
lemmaSwapFoldEquivF      {G = |Ef|  _}  {e = ⟨ e ⟩}      prf = refl
lemmaSwapFoldEquivF {F}  {G₁ |+| G₂}    {e = inj₁ x₁}    prf 
  = cong inj₁ (lemmaSwapFoldEquivF {F} {G₁} prf) 
lemmaSwapFoldEquivF {F}  {G₁ |+| G₂}    {e = inj₂ y₁}    prf 
  = cong inj₂ (lemmaSwapFoldEquivF {F} {G₂} prf) 
lemmaSwapFoldEquivF {F}  {G₁ |x| G₂}    {e = e₁ , e₂}    prf
  = cong₂ (_,_)  (lemmaSwapFoldEquivF {F} {G₁} {e = e₁} prf) 
                 (lemmaSwapFoldEquivF {F} {G₂} {e = e₂} prf)
lemmaSwapFoldEquivF {F} {|B| S G} {H} {S'} 
                                        {e = z , e}      prf with S ≟S S'
... | yes _ = cong₂ (_,_) refl (lemmaSwapFoldEquivF {F} {G} {H} {S'} {e = e} prf) 
... | no _  = cong₂ (_,_) refl (lemmaSwapFoldEquivF {F} {G} {H} {S'} {e = e} prf) 
\end{code}

%<*swapfoldequiv>
\begin{code}
lemmaSwapFoldEquiv  :  {F H : Functor}{S : Sort}
      {x y : V}{e : μ F}{f  : ⟦ F ⟧ (μ H) → μ H}
   →  ({x y : V}   {e  : ⟦ F ⟧ (μ H)} 
                   → f (swapF F S x y e) ≡ swap {H} S x y (f e))
   →  fold F f (swap S x y e) ≡ swap S x y (fold F f e)
\end{code}
%</swapfoldequiv>

\begin{code}
lemmaSwapFoldEquiv {F} {H} {S} {x} {y} {e} prf = lemmaSwapFoldEquivF {F} {|R|} {H} {S} {x} {y} {e} prf

lemmaSwapFoldEquivCtxF :  {F G H : Functor}{S : Sort}{x y : V}{e : ⟦ G ⟧ (μ F)}{f  : V → V → ⟦ F ⟧ (μ H) → μ H}
                      {g  : ⟦ F ⟧ (μ H) → μ H}
                      → ({x y : V}{e  : ⟦ F ⟧ (μ H)} → f x y (swapF F S x y e) ≡ swap {H} S x y (g e))
                      → foldmap F G (f x y) (swapF G S x y e) ≡ swapF G S x y (foldmap F G g e)
lemmaSwapFoldEquivCtxF {G = |v| x} prf = refl
lemmaSwapFoldEquivCtxF {G = |1|} prf = refl
lemmaSwapFoldEquivCtxF {F} {|R|} {x = x} {y} {⟨ e ⟩} {f} prf = trans (cong (f x y) (lemmaSwapFoldEquivCtxF {F} {F} prf)) prf
lemmaSwapFoldEquivCtxF {G = |E| x} prf = refl
lemmaSwapFoldEquivCtxF {G = |Ef| G} {e = ⟨ e ⟩} prf = refl
lemmaSwapFoldEquivCtxF {F} {G₁ |+| G₂} {e = inj₁ x₁} prf = cong inj₁ (lemmaSwapFoldEquivCtxF {F} {G₁} prf)  
lemmaSwapFoldEquivCtxF {F} {G₁ |+| G₂} {e = inj₂ y₁} prf = cong inj₂ (lemmaSwapFoldEquivCtxF {F} {G₂} prf)  
lemmaSwapFoldEquivCtxF {F} {G₁ |x| G₂} {e = e₁ , e₂} prf
  = cong₂ (_,_) (lemmaSwapFoldEquivCtxF {F} {G₁} {e = e₁} prf) (lemmaSwapFoldEquivCtxF {F} {G₂} {e = e₂} prf) 
lemmaSwapFoldEquivCtxF {F} {|B| S G} {S = S'} {e = z , e} prf with S ≟S S'
... | yes _ = cong₂ (_,_) refl (lemmaSwapFoldEquivCtxF {F} {G} {S = S'} {e = e} prf)
... | no _  = cong₂ (_,_) refl (lemmaSwapFoldEquivCtxF {F} {G} {S = S'} {e = e} prf)
\end{code}

-- lemmaSwapFoldSEquivF :  {C H F G : Functor}{S : Sort}{x y : V}
--    {e : ⟦ G ⟧ (μ F)}{f  : μ C → ⟦ F ⟧ (μ H) → μ H}{c : μ C}
--    → ({x y : V}{e  : ⟦ F ⟧ (μ H)} → f (swap {C} S x y c) (swapF F S x y e) ≡ swap {H} S x y (f c e))
--    → foldmapCtx F G f (swap {C} S x y c) (swapF G S x y e) ≡ swapF G S x y (foldmapCtx F G f c e)
-- lemmaSwapFoldSEquivF {G = |v| x} prf = refl
-- lemmaSwapFoldSEquivF {G = |1|} prf =  refl
-- lemmaSwapFoldSEquivF {C} {H} {F} {|R|} {S} {x} {y} {⟨ e ⟩} {f} {c} prf
--   =  begin≡
--        f (swap {C} S x y c) (foldmapCtx F F f (swap {C} S x y c) (swapF F S x y e))
--      ≡⟨ cong (f (swap {C} S x y c)) (lemmaSwapFoldSEquivF {C} {H} {F} {F} {S} {x} {y} {e} {f} {c} prf) ⟩
--        f (swap {C} S x y c) (swapF F S x y (foldmapCtx F F f c e))
--      ≡⟨ prf ⟩
--        swapF |R| S x y (f c (foldmapCtx F F f c e))
--      ■
-- lemmaSwapFoldSEquivF {G = |E| x} prf =  refl
-- lemmaSwapFoldSEquivF {G = |Ef| G} {e = ⟨ e ⟩} prf =  refl
-- lemmaSwapFoldSEquivF {G = G |+| G₁} {e = inj₁ e} prf = cong inj₁ (lemmaSwapFoldSEquivF {G = G } {e = e} prf)
-- lemmaSwapFoldSEquivF {G = G |+| G₁} {e = inj₂ e} prf = cong inj₂ (lemmaSwapFoldSEquivF {G = G₁ } {e = e} prf)
-- lemmaSwapFoldSEquivF {G = G |x| G₁} {e = e , e₁} prf
--   = cong₂ (_,_) (lemmaSwapFoldSEquivF {G = G} {e = e} prf) (lemmaSwapFoldSEquivF {G = G₁} {e = e₁} prf)
-- lemmaSwapFoldSEquivF {G = |B| S G} {S = S'} {e = z , e} prf with S ≟S S'
-- ... | yes _ = cong₂ (_,_) refl (lemmaSwapFoldSEquivF {G = G} {S = S'} {e = e} prf) 
-- ... | no _ = cong₂ (_,_) refl (lemmaSwapFoldSEquivF {G = G} {S = S'} {e = e} prf) 


%<*swapfoldCtx>
\begin{code}
lemmaSwapFoldCtxEquiv : {C H F  : Functor}{S : Sort}{x y : V}
      {e : μ F}{f : μ C → ⟦ F ⟧ (μ H) → μ H}{c : μ C}
   →  ({c : μ C}{S  : Sort}{x y : V}{e : ⟦ F ⟧ (μ H)}
                    → f (swap S x y c) (swapF F S x y e) ≡ swap S x y (f c e))
   →  foldCtx F f (swap {C} S x y c) (swap {F} S x y e) ≡ swap {H} S x y (foldCtx F f c e)
\end{code}
%</swapfoldCtx>

%<*swapfoldCtxproof>
\begin{code}
lemmaSwapFoldCtxEquiv {C} {H} {F} {S} {x} {y} {⟨ e ⟩} {f} {c} prf =
    begin≡
      foldCtx F f (swap {C} S x y c) (swap {F} S x y ⟨ e ⟩)
    ≡⟨ refl                                                       ⟩
      f  (swap {C} S x y c) 
         (foldmap F F (f (swapF |R| S x y c)) (swapF F S x y e))
   ≡⟨ cong  (f (swap {C} S x y c)) 
            (lemmaSwapFoldEquivCtxF {F} {F} {H} {S} {x} {y} {e} 
                     {λ x y → f (swap {C} S x y c)} {f c} prf)    ⟩
      f (swap {C} S x y c) (swapF F S x y (foldmap F F (f c) e))
    ≡⟨ prf                                                        ⟩
      swap {H} S x y (foldCtx F f c ⟨ e ⟩)
    ■
\end{code}
%</swapfoldCtxproof>

-- \begin{code}
-- --lemmaSwapFoldSEquiv {C} {H} {F} {S} {x} {y} {⟨ e ⟩} {f} {c} prf
-- -- begin≡
-- --       foldCtx F f (swap {C} S x y c) (swap {F} S x y ⟨ e ⟩)
-- --     ≡⟨ refl ⟩
-- --       f (swap {C} S x y c) (foldmapCtx F F f (swapF |R| S x y c) (swapF F S x y e))
-- --     ≡⟨ cong (f (swap {C} S x y c)) (lemmaSwapFoldSEquivF {C} {H} {F} {F} {S} {x} {y} {e} {f} {c} prf) ⟩
-- --       f (swap {C} S x y c) (swapF F S x y (foldmapCtx F F f c e))
-- --     ≡⟨ prf ⟩
-- --       swap {H} S x y (foldCtx F f c ⟨ e ⟩)
-- --     ■
-- \end{code}

