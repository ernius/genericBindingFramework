\begin{code}
module Fresh where

open import Atom
open import GPBindings
open import Swap

open import Data.Empty
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
lemmaSwapF# : {F G : Functor}{S : Sort}{x y : V}{e  : ⟦ G ⟧ (μ F)}
        → freshF S y G e
        → freshF S x G (swapF G S x y e)
lemmaSwapF# {F} {|1|}        {S} {x} {y} {e}        y#e                 = fresh1
lemmaSwapF# {F} {|R|}        {S} {x} {y} {⟨ e ⟩}    (freshR y#e)        = freshR (lemmaSwapF# y#e)
lemmaSwapF# {F} {|E| A}      {S} {x} {y} {e}        y#e                 = freshE
lemmaSwapF# {F} {|Ef| G}     {S} {x} {y} {⟨ e ⟩}    (freshEf y#e)       = freshEf (lemmaSwapF# y#e) 
lemmaSwapF# {F} {G₁ |+| G₂}  {S} {x} {y} {inj₁ e}   (freshinj₁ y#e)     = freshinj₁ (lemmaSwapF# y#e) 
lemmaSwapF# {F} {G₁ |+| G₂}  {S} {x} {y} {inj₂ e}   (freshinj₂ y#e)     = freshinj₂ (lemmaSwapF# y#e) 
lemmaSwapF# {F} {G₁ |x| G₂}  {S} {x} {y} {e₁ , e₂}  (freshx y#e₁ y#e₂)  = freshx (lemmaSwapF# y#e₁) (lemmaSwapF# y#e₂)
lemmaSwapF# {F} {|v| S′}     {S} {x} {y} {z}        (freshV≢ y≢z) with S′ ≟S S
... | no  S′≢S                                                          = freshV≢S S′≢S
... | yes _    with （ x ∙ y ）ₐ z | lemma∙ₐ x y z
lemmaSwapF# {F} {|v| S′}     {S} {x} {y} {.x}       (freshV≢ y≢x)  | yes _
               | .y | inj₁ (refl , refl)                                = freshV≢ (sym≢ y≢x)
lemmaSwapF# {F} {|v| S′}     {S} {x} {y} {.y}       (freshV≢ y≢y)  | yes _
               | .x | inj₂ (inj₁ (refl , z≢x , refl))                   = ⊥-elim (y≢y refl)  
lemmaSwapF# {F} {|v| S′}     {S} {x} {y} {z}        (freshV≢ y≢z)  | yes _
               | .z | inj₂ (inj₂ (z≢x , z≢y , refl))                    = freshV≢ (sym≢ z≢x)
lemmaSwapF# {F} {|v| S′}     {S} {x} {y} {z}        (freshV≢S S′≢S)     = freshV≢S S′≢S
lemmaSwapF# {F} {|B| .S G}   {S} {x} {y} {.y , e}   freshb≡  with S ≟S S
... | no  S≢S                                                           = ⊥-elim (S≢S refl) 
... | yes _  with （ x ∙ y ）ₐ y | lemma∙ₐc≡b x y y refl
...          | .x | refl                                                = freshb≡
lemmaSwapF# {F} {|B| S′ G}   {S} {x} {y} {z , e}    (freshb y#e) with S′ ≟S S
... | yes _                                                             = freshb (lemmaSwapF#  y#e)
... | no  _                                                             = freshb (lemmaSwapF#  y#e)

lemmaSwapF#≢S→ : {F G : Functor}{S S′ : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → S ≢ S′      
        → freshF S x G (swapF G S′ y z e)
        → freshF S x G e
lemmaSwapF#≢S→ {F} {|1|}       {S} {S′} {x} {y} {z} {e}       S≢S′ x#（yz）e                       = fresh1
lemmaSwapF#≢S→ {F} {|R|}       {S} {S′} {x} {y} {z} {⟨ e ⟩}   S≢S′ (freshR x#（yz）e)              = freshR (lemmaSwapF#≢S→ S≢S′ x#（yz）e)
lemmaSwapF#≢S→ {F} {|E| x}     {S} {S′} {x₁} {y} {z} {e}      S≢S′ x#（yz）e                       = freshE
lemmaSwapF#≢S→ {F} {|Ef| G}    {S} {S′} {x} {y} {z} {⟨ e ⟩}   S≢S′ (freshEf x#（yz）e)             = freshEf (lemmaSwapF#≢S→ S≢S′ x#（yz）e)
lemmaSwapF#≢S→ {F} {G |+| G₁}  {S} {S′} {x} {y} {z} {inj₁ e}  S≢S′ (freshinj₁ x#（yz）e)           = freshinj₁ (lemmaSwapF#≢S→ S≢S′ x#（yz）e)
lemmaSwapF#≢S→ {F} {G |+| G₁}  {S} {S′} {x} {y} {z} {inj₂ e}  S≢S′ (freshinj₂ x#（yz）e)           = freshinj₂ (lemmaSwapF#≢S→ S≢S′ x#（yz）e)
lemmaSwapF#≢S→ {F} {G₁ |x| G₂} {S} {S′} {x} {y} {z} {e₁ , e₂} S≢S′ (freshx x#（yz）e₁ x#（yz）e₂)   = freshx (lemmaSwapF#≢S→ S≢S′ x#（yz）e₁) (lemmaSwapF#≢S→ S≢S′ x#（yz）e₂)
lemmaSwapF#≢S→ {F} {|v| S″}    {S} {S′} {x} {y} {z} {w}       S≢S′ x#（yz）w
  with S″ ≟S S′
... | no  S″≢S′ = x#（yz）w
lemmaSwapF#≢S→ {F} {|v| .S′}    {S} {S′} {x} {y} {z} {w}      S≢S′ x#（yz）w
    | yes refl  = freshV≢S (sym≢ S≢S′)
lemmaSwapF#≢S→ {F} {|B| S G}   {.S} {S′} {x} {y} {z} {w , e}  S≢S′ freshb≡            with S ≟S S′
... | yes S≡S′  = ⊥-elim (S≢S′ S≡S′)
lemmaSwapF#≢S→ {F} {|B| S G}   {.S} {S′} .{（ y ∙ z ）ₐ w} {y} {z} {w , e}  S≢S′ freshb≡  
    | no  _     = freshb≡
lemmaSwapF#≢S→ {F} {|B| S″ G}   {S} {S′} {x} {y} {z} {w , e}  S≢S′ (freshb x#（yz）e)  with S″ ≟S S′
... | yes _ = freshb (lemmaSwapF#≢S→ S≢S′ x#（yz）e)
... | no  _ = freshb (lemmaSwapF#≢S→ S≢S′ x#（yz）e)

lemmaSwapF#≢S← : {F G : Functor}{S S' : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → S ≢ S'      
        → freshF S x G e
        → freshF S x G (swapF G S' y z e)
lemmaSwapF#≢S← {F} {|1|}       {S} {S′} {x} {y} {z} {e}       S≢S′ x#（yz）e                       = fresh1
lemmaSwapF#≢S← {F} {|R|}       {S} {S′} {x} {y} {z} {⟨ e ⟩}   S≢S′ (freshR x#（yz）e)              = freshR (lemmaSwapF#≢S← S≢S′ x#（yz）e)
lemmaSwapF#≢S← {F} {|E| x}     {S} {S′} {x₁} {y} {z} {e}      S≢S′ x#（yz）e                       = freshE
lemmaSwapF#≢S← {F} {|Ef| G}    {S} {S′} {x} {y} {z} {⟨ e ⟩}   S≢S′ (freshEf x#（yz）e)             = freshEf (lemmaSwapF#≢S← S≢S′ x#（yz）e)
lemmaSwapF#≢S← {F} {G |+| G₁}  {S} {S′} {x} {y} {z} {inj₁ e}  S≢S′ (freshinj₁ x#（yz）e)           = freshinj₁ (lemmaSwapF#≢S← S≢S′ x#（yz）e)
lemmaSwapF#≢S← {F} {G |+| G₁}  {S} {S′} {x} {y} {z} {inj₂ e}  S≢S′ (freshinj₂ x#（yz）e)           = freshinj₂ (lemmaSwapF#≢S← S≢S′ x#（yz）e)
lemmaSwapF#≢S← {F} {G₁ |x| G₂} {S} {S′} {x} {y} {z} {e₁ , e₂} S≢S′ (freshx x#（yz）e₁ x#（yz）e₂)   = freshx (lemmaSwapF#≢S← S≢S′ x#（yz）e₁) (lemmaSwapF#≢S← S≢S′ x#（yz）e₂)
lemmaSwapF#≢S← {F} {|v| S″}    {S} {S′} {x} {y} {z} {w}       S≢S′ x#（yz）w
  with S″ ≟S S′
... | no  S″≢S′ = x#（yz）w
lemmaSwapF#≢S← {F} {|v| .S′}    {S} {S′} {x} {y} {z} {w}      S≢S′ x#（yz）w
    | yes refl  = freshV≢S (sym≢ S≢S′)
lemmaSwapF#≢S← {F} {|B| S G}   {.S} {S′} {x} {y} {z} {w , e}  S≢S′ freshb≡            with S ≟S S′
... | yes S≡S′  = ⊥-elim (S≢S′ S≡S′)
lemmaSwapF#≢S← {F} {|B| S G}   {.S} {S′} .{（ y ∙ z ）ₐ w} {y} {z} {w , e}  S≢S′ freshb≡  
    | no  _     = freshb≡
lemmaSwapF#≢S← {F} {|B| S″ G}   {S} {S′} {x} {y} {z} {w , e}  S≢S′ (freshb x#（yz）e)  with S″ ≟S S′
... | yes _ = freshb (lemmaSwapF#≢S← S≢S′ x#（yz）e)
... | no  _ = freshb (lemmaSwapF#≢S← S≢S′ x#（yz）e)

lemmaSwapF#≢→ : {F G : Functor}{S : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → x ≢ y → x ≢ z 
        → freshF S x G (swapF G S y z e)
        → freshF S x G e
lemmaSwapF#≢→ {F} {|1|}       {S}  {x} {y} {z} {e}       x≢y x≢z x#（yz）e                       = fresh1
lemmaSwapF#≢→ {F} {|R|}       {S}  {x} {y} {z} {⟨ e ⟩}   x≢y x≢z (freshR x#（yz）e)              = freshR (lemmaSwapF#≢→ x≢y x≢z x#（yz）e)
lemmaSwapF#≢→ {F} {|E| x}     {S}  {x₁} {y} {z} {e}      x≢y x≢z x#（yz）e                       = freshE
lemmaSwapF#≢→ {F} {|Ef| G}    {S}  {x} {y} {z} {⟨ e ⟩}   x≢y x≢z (freshEf x#（yz）e)             = freshEf (lemmaSwapF#≢→ x≢y x≢z x#（yz）e)
lemmaSwapF#≢→ {F} {G |+| G₁}  {S}  {x} {y} {z} {inj₁ e}  x≢y x≢z (freshinj₁ x#（yz）e)           = freshinj₁ (lemmaSwapF#≢→ x≢y x≢z x#（yz）e)
lemmaSwapF#≢→ {F} {G |+| G₁}  {S}  {x} {y} {z} {inj₂ e}  x≢y x≢z (freshinj₂ x#（yz）e)           = freshinj₂ (lemmaSwapF#≢→ x≢y x≢z x#（yz）e)
lemmaSwapF#≢→ {F} {G₁ |x| G₂} {S}  {x} {y} {z} {e₁ , e₂} x≢y x≢z (freshx x#（yz）e₁ x#（yz）e₂)   = freshx (lemmaSwapF#≢→ x≢y x≢z x#（yz）e₁) (lemmaSwapF#≢→ x≢y x≢z x#（yz）e₂)
lemmaSwapF#≢→ {F} {|v| S′}    {S}  {x} {y} {z} {w}       x≢y x≢z x#（yz）w           with S′ ≟S S
... | no  S′≢S′ = x#（yz）w
lemmaSwapF#≢→ {F} {|v| .S}    {S}  {x} {y} {z} {w}      x≢y x≢z x#（yz）w            
    | yes refl with S ≟S S
...            | no S≢S = ⊥-elim (S≢S refl)
lemmaSwapF#≢→ {F} {|v| .S}    {S}  {x} {y} {z} {w}      x≢y x≢z (freshV≢ x≢（yz）w)
    | yes refl | yes _  = freshV≢ (lemma∙ₐa≢b∧a≢c∧a≢（bc）d→a≢d x≢y x≢z x≢（yz）w)
lemmaSwapF#≢→ {F} {|v| .S}    {S}  {x} {y} {z} {w}      x≢y x≢z (freshV≢S S≢S)            
    | yes refl | yes _  = ⊥-elim (S≢S refl)
lemmaSwapF#≢→ {F} {|B| S G}   {.S}  {x} {y} {z} {w , e}  x≢y x≢z freshb≡            with S ≟S S
... | yes S≡S with （ y ∙ z ）ₐ w | lemma∙ₐ（ab）c≢a∧（ab）c≢b→（ab）c≡a {y} {z} {w} x≢y x≢z
...           |  .w  | refl = freshb≡ 
lemmaSwapF#≢→ {F} {|B| S G}   {.S}  .{（ y ∙ z ）ₐ w} {y} {z} {w , e}  x≢y x≢z freshb≡  
    | no  S≢S  = ⊥-elim (S≢S refl)
lemmaSwapF#≢→ {F} {|B| S″ G}   {S}  {x} {y} {z} {w , e}  x≢y x≢z (freshb x#（yz）e)  with S″ ≟S S
... | yes _ = freshb (lemmaSwapF#≢→ x≢y x≢z x#（yz）e)
... | no  _ = freshb (lemmaSwapF#≢→ x≢y x≢z x#（yz）e)

lemmaSwapF#≢← : {F G : Functor}{S : Sort}{x y z : V}{e  : ⟦ G ⟧ (μ F)}
        → x ≢ y → x ≢ z 
        → freshF S x G e
        → freshF S x G (swapF G S y z e)
lemmaSwapF#≢← {F} {|1|}       {S}  {x} {y} {z} {e}       x≢y x≢z x#（yz）e                       = fresh1
lemmaSwapF#≢← {F} {|R|}       {S}  {x} {y} {z} {⟨ e ⟩}   x≢y x≢z (freshR x#（yz）e)              = freshR (lemmaSwapF#≢← x≢y x≢z x#（yz）e)
lemmaSwapF#≢← {F} {|E| x}     {S}  {x₁} {y} {z} {e}      x≢y x≢z x#（yz）e                       = freshE
lemmaSwapF#≢← {F} {|Ef| G}    {S}  {x} {y} {z} {⟨ e ⟩}   x≢y x≢z (freshEf x#（yz）e)             = freshEf (lemmaSwapF#≢← x≢y x≢z x#（yz）e)
lemmaSwapF#≢← {F} {G |+| G₁}  {S}  {x} {y} {z} {inj₁ e}  x≢y x≢z (freshinj₁ x#（yz）e)           = freshinj₁ (lemmaSwapF#≢← x≢y x≢z x#（yz）e)
lemmaSwapF#≢← {F} {G |+| G₁}  {S}  {x} {y} {z} {inj₂ e}  x≢y x≢z (freshinj₂ x#（yz）e)           = freshinj₂ (lemmaSwapF#≢← x≢y x≢z x#（yz）e)
lemmaSwapF#≢← {F} {G₁ |x| G₂} {S}  {x} {y} {z} {e₁ , e₂} x≢y x≢z (freshx x#（yz）e₁ x#（yz）e₂)   = freshx (lemmaSwapF#≢← x≢y x≢z x#（yz）e₁) (lemmaSwapF#≢← x≢y x≢z x#（yz）e₂)
lemmaSwapF#≢← {F} {|v| S′}    {S}  {x} {y} {z} {w}       x≢y x≢z x#（yz）w           with S′ ≟S S
... | no  S′≢S′ = x#（yz）w
lemmaSwapF#≢← {F} {|v| .S}    {S}  {x} {y} {z} {w}      x≢y x≢z x#（yz）w            
    | yes refl with S ≟S S
...            | no S≢S = ⊥-elim (S≢S refl)
lemmaSwapF#≢← {F} {|v| .S}    {S}  {x} {y} {z} {w}      x≢y x≢z (freshV≢ x≢（yz）w)
    | yes refl | yes _  = freshV≢ (lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d x≢y x≢z x≢（yz）w)
lemmaSwapF#≢← {F} {|v| .S}    {S}  {x} {y} {z} {w}      x≢y x≢z (freshV≢S S≢S)            
    | yes refl | yes _  = ⊥-elim (S≢S refl)
lemmaSwapF#≢← {F} {|B| S G}   {.S}  {x} {y} {z} {w , e}  x≢y x≢z freshb≡            with S ≟S S
... | yes S≡S  with （ y ∙ z ）ₐ w | lemma∙ₐc≢a∧c≢b x≢y x≢z
...            | .w  | refl = freshb≡ 
lemmaSwapF#≢← {F} {|B| S G}   {.S}  .{（ y ∙ z ）ₐ w} {y} {z} {w , e}  x≢y x≢z freshb≡  
    | no  S≢S  = ⊥-elim (S≢S refl)
lemmaSwapF#≢← {F} {|B| S″ G}   {S}  {x} {y} {z} {w , e}  x≢y x≢z (freshb x#（yz）e)  with S″ ≟S S
... | yes _ = freshb (lemmaSwapF#≢← x≢y x≢z x#（yz）e)
... | no  _ = freshb (lemmaSwapF#≢← x≢y x≢z x#（yz）e)
\end{code}
