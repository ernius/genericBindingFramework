\begin{code}
module GPBindings where

open import Function
open import Data.Nat hiding (fold)
open import Data.Bool
open import Data.List hiding (unfold)
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Data.Sum
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Atom

infixr 20 _|+|_
infixr 21 _|x|_

Sort  = ℕ
V     = Atom
_≟v_  = Data.Nat._≟_
_≟S_  = Data.Nat._≟_
\end{code}

%<*functor>
\begin{code}
data Functor : Set₁ where               
  |1|    :                        Functor
  |R|    :                        Functor
  |E|    : Set                 →  Functor        
  |Ef|   : Functor             →  Functor        
  _|+|_  : Functor  → Functor  →  Functor     
  _|x|_  : Functor  → Functor  →  Functor
  |v|    : Sort                →  Functor
  |B|    : Sort     → Functor  →  Functor
\end{code}
%</functor>

%<*interpret>
\begin{code}
mutual
  ⟦_⟧ : Functor → Set → Set           
  ⟦ |1|        ⟧ _  = ⊤
  ⟦ |R|        ⟧ A  = A
  ⟦ |E|     B  ⟧ _  = B
  ⟦ |Ef|    F  ⟧ _  = μ F
  ⟦ F |+|   G  ⟧ A  = ⟦ F ⟧ A  ⊎ ⟦ G ⟧ A
  ⟦ F |x|   G  ⟧ A  = ⟦ F ⟧ A  × ⟦ G ⟧ A
  ⟦ |v|  S     ⟧ _  = V
  ⟦ |B|  S  G  ⟧ A  = V        × ⟦ G ⟧ A
\end{code}
%</interpret>

%<*mu>
\begin{code}
  data μ (F : Functor) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F
\end{code}
%</mu>


%<*foldtermination>
\begin{code}
mapF : {A B : Set}(F : Functor) → (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B 
mapF (|v|   S)     f x          = x
mapF |1|           f tt         = tt
mapF (|E|   A)     f e          = e
mapF (|Ef|  F)     f e          = e
mapF |R|           f e          = f e
mapF (G₁ |+|  G₂)  f (inj₁ e)   = inj₁  (mapF G₁ f e)
mapF (G₁ |+|  G₂)  f (inj₂ e)   = inj₂  (mapF G₂ f e) 
mapF (G₁ |x|  G₂)  f (e₁ , e₂)  = mapF G₁ f e₁  , mapF G₂  f e₂
mapF (|B|  S  G)   f (x , e)    = x             , mapF G   f e
\end{code}
%</foldtermination>


%<*foldtermination2>
\begin{code}
{-# TERMINATING #-}
foldT : {A : Set}(F : Functor) → (⟦ F ⟧ A → A) → μ F → A
foldT F f ⟨ e ⟩ = f (mapF F (foldT F f) e)
\end{code}
%</foldtermination2>


--unfold : {F : Functor} → μ F → ⟦ F ⟧ (μ F)
--unfold ⟨ e ⟩ = e

%<*foldmap>
\begin{code}
foldmap :  {A : Set}(F G  : Functor) →  (⟦ F ⟧ A → A) →  ⟦ G ⟧ (μ F) → ⟦ G ⟧ A
foldmap F |1|           f tt         =  tt 
foldmap F |R|           f ⟨ e ⟩      =  f     (foldmap F F   f e) 
foldmap F (|E|   A)     f e          =  e
foldmap F (|Ef|  G)     f e          =  e
foldmap F (G₁ |+|  G₂)  f (inj₁ e)   =  inj₁  (foldmap F G₁  f e)
foldmap F (G₁ |+|  G₂)  f (inj₂ e)   =  inj₂  (foldmap F G₂  f e)
foldmap F (G₁ |x|  G₂)  f (e₁ , e₂)  =  foldmap F G₁ f e₁   , foldmap F G₂  f e₂
foldmap F (|v|   S)     f x          =  x
foldmap F (|B| S   G)   f (x , e)    =  x                   , foldmap F G   f e
\end{code}
%</foldmap>

%<*foldmap2>
\begin{code}
fold : {A : Set}(F : Functor) → (⟦ F ⟧ A → A) → μ F → A
fold F f e = foldmap F |R| f e 
\end{code}
%</foldmap2>

Recursion

\begin{code}
recmap :  {A : Set}(F G  : Functor)
       →  (⟦ F ⟧ (A × μ F) → A) 
       →  ⟦ G ⟧ (μ F) → ⟦ G ⟧ (A × μ F) 
recmap F (|v| S)      f x              = x  
recmap F |1|          f tt             = tt 
recmap F (|E| A)      f e              = e  
recmap F (|Ef| G)     f e              = e  
recmap F |R|          f ⟨ e ⟩          = f (recmap F F f e) , ⟨ e ⟩
recmap F (G₁ |+| G₂)  f (inj₁ e)       = inj₁   (recmap F G₁  f e) 
recmap F (G₁ |+| G₂)  f (inj₂ e)       = inj₂   (recmap F G₂  f e)
recmap F (G₁ |x| G₂)  f (e₁ , e₂)      = recmap F G₁ f e₁   , recmap F G₂ f e₂ 
recmap F (|B| S G)    f (x , e)        = x                  , recmap F G   f e

rec : {A : Set}{F : Functor} → (⟦ F ⟧ (A × μ F) → A) → μ F → A
rec {F = F} f e = proj₁ (recmap F |R| f e)
\end{code}

Now the function $f$\ has an explicit context $\mu C$, and the returned type is a functorial one.

-- foldmapCtx  :  {C H : Functor}(F G  : Functor)
--             →  (μ C → ⟦ F ⟧ (μ H)  → μ H)
--             →  μ C →  ⟦ G ⟧ (μ F) → ⟦ G ⟧ (μ H)
-- foldmapCtx F (|v|   S)     f c x          =  x
-- foldmapCtx F |1|           f c tt         =  tt
-- foldmapCtx F (|E|   A)     f c e          =  e
-- foldmapCtx F (|Ef|  G)     f c e          =  e
-- foldmapCtx F |R|           f c ⟨ e ⟩      =  f c   (foldmapCtx F F   f c e) 
-- foldmapCtx F (G₁ |+|  G₂)  f c (inj₁ e)   =  inj₁  (foldmapCtx F G₁  f c e)
-- foldmapCtx F (G₁ |+|  G₂)  f c (inj₂ e)   =  inj₂  (foldmapCtx F G₂  f c e)
-- foldmapCtx F (G₁ |x|  G₂)  f c (e₁ , e₂)  =  foldmapCtx F G₁  f c e₁   , 
--                                              foldmapCtx F G₂  f c e₂
-- foldmapCtx F (|B| S   G)   f c (x , e)    =  x                        , 
--                                              foldmapCtx F G   f c e
-- foldCtx {C} {H} F f c = foldmapCtx {C} {H} F |R| f c

%<*foldCtx>
\begin{code}
foldCtx : {C H : Functor}(F : Functor) → (μ C → ⟦ F ⟧ (μ H) → μ H) → μ C → μ F → μ H
foldCtx F f c = fold F (f c)
\end{code}
%</foldCtx>

-- recmapCtx :  {C H : Functor}(F G  : Functor)
--               → (μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F))  → μ H)
--               → μ C →  ⟦ G ⟧ (μ F) → ⟦ G ⟧ (μ (|Ef| H |x| |Ef| F))
-- recmapCtx F (|v| S)      f c x          =  x
-- recmapCtx F |1|          f c tt         =  tt
-- recmapCtx F (|E| A)      f c e          =  e
-- recmapCtx F (|Ef| G)     f c e          =  e
-- recmapCtx F |R|          f c ⟨ e ⟩      =  ⟨ f c  (recmapCtx F F   f c e) , ⟨ e ⟩ ⟩
-- recmapCtx F (G₁ |+| G₂)  f c (inj₁ e)   =  inj₁   (recmapCtx F G₁  f c e)
-- recmapCtx F (G₁ |+| G₂)  f c (inj₂ e)   =  inj₂   (recmapCtx F G₂  f c e)
-- recmapCtx F (G₁ |x| G₂)  f c (e₁ , e₂)  =  recmapCtx F G₁  f c e₁  , 
--                                            recmapCtx F G₂  f c e₂
-- recmapCtx F (|B| S G)    f c (x , e)    =  x                      , 
--                                            recmapCtx F G   f c e

-- recCtx :  {C H : Functor}(F : Functor)
--            → (μ C → ⟦ F ⟧ (μ (|Ef| H |x| |Ef| F)) → μ H) -- (μ H × μ F)
--            → μ C → μ F → μ H
-- recCtx {C} {H} F f c e with recmapCtx {C} {H} F |R| f c e
-- ... | ⟨ h , _ ⟩ = h

Recursion with contexts.

\begin{code}
recCtx :  {C H : Functor}(F : Functor)
           → (μ C → ⟦ F ⟧ (μ H × μ F) → μ H) -- (μ H × μ F)
           → μ C → μ F → μ H
recCtx {C} {H} F f c = rec {μ H} {F} (f c)
\end{code}

-- fold fusion
-- lemma-foldSFusion : {C H : Functor}(F : Functor)(f : μ C → ⟦ F ⟧ (μ H) → μ H)
-- {μ C → μ F → μ H                f ∘ foldS F f c ≡ foldS F f' c'

-- mapFh : {F : Functor}(G : Functor)(P : μ F → Set) → ((a : μ F) → P a) → (x : ⟦ G ⟧ (μ F)) → fih G P x
-- mapFh (|v| S)    P f n        = tt

-- mapFh |1|        P f tt       = tt
-- mapFh (|E| B)    P f b        = tt
-- mapFh (|Ef| G)   P f b        = tt
-- mapFh |R|        P f x        = f x
-- mapFh (G |+| G') P f (inj₁ x) = mapFh G  P f x
-- mapFh (G |+| G') P f (inj₂ y) = mapFh G' P f y
-- mapFh (G |x| G') P f (x , y)  = mapFh G  P f x , mapFh G' P f y
-- mapFh (|B| S G)  P f (x , y)  = mapFh G  P f y

-- {-# TERMINATING #-}
-- foldInd : (F : Functor)(P : μ F → Set)    
--   → ((e : ⟦ F ⟧ (μ F)) → fih F P e →  P ⟨ e ⟩)  
--   → (e : μ F) → P e
-- foldInd F P hi ⟨ e ⟩ = hi e (mapFh F P (foldInd F P hi) e)

Primitive Induction

%<*primIndih>
\begin{code}
fih  :  {F : Functor}(G : Functor)(P : μ F → Set) → ⟦ G ⟧ (μ F) → Set
fih |1|           P tt          = ⊤
fih |R|           P e           = P e
fih (|E|   B)     P e           = ⊤
fih (|Ef|  G)     P e           = ⊤
fih (G₁ |+|  G₂)  P (inj₁  e)   = fih G₁  P e
fih (G₁ |+|  G₂)  P (inj₂  e)   = fih G₂  P e 
fih (G₁ |x|  G₂)  P (e₁ ,  e₂)  = fih G₁  P e₁ × fih G₂ P e₂
fih (|v|   S)     P x           = ⊤
fih (|B| S   G)   P (x ,   e)   = fih G   P e
\end{code}
%</primIndih>

%<*primInd>
\begin{code}
foldmapFh :  {F : Functor}(G : Functor)(P : μ F → Set)
             → ((e : ⟦ F ⟧ (μ F)) → fih F P e →  P ⟨ e ⟩) → (x : ⟦ G ⟧ (μ F)) → fih G P x
foldmapFh |1|           P hi tt          =  tt
foldmapFh {F} |R|       P hi ⟨ e ⟩       =  hi e (foldmapFh {F} F P hi e) 
foldmapFh (|E|   B)     P hi b           =  tt
foldmapFh (|Ef|  F)     P hi b           =  tt
foldmapFh (G₁ |+|  G₂)  P hi (inj₁  e)   =  foldmapFh G₁  P hi e
foldmapFh (G₁ |+|  G₂)  P hi (inj₂  e)   =  foldmapFh G₂  P hi e
foldmapFh (G₁ |x|  G₂)  P hi (e₁  , e₂)  =  foldmapFh G₁  P hi e₁ , foldmapFh G₂  P hi e₂
foldmapFh (|v|   S)     P hi n           =  tt
foldmapFh (|B| S   G)   P hi (x   , e)   =  foldmapFh G   P hi e
\end{code}
%</primInd>


%<*primInd2>
\begin{code}
foldInd : (F : Functor)(P : μ F → Set) → ((e : ⟦ F ⟧ (μ F)) → fih F P e →  P ⟨ e ⟩) → (e : μ F) → P e
foldInd F P hi e = foldmapFh {F} |R| P hi e
\end{code}
%</primInd2>



%</primInd>

Size

\begin{code}
sizeF : {F : Functor}(G : Functor) → ⟦ G ⟧ (μ F) → ℕ
sizeF (|v| x)     e          = 1
sizeF |1|         e          = 1
sizeF (|E| x)     e          = 1
sizeF (|Ef| G)    ⟨ e ⟩      = sizeF G e
sizeF {F} |R|     ⟨ e ⟩      = sizeF F e
sizeF (G₁ |+| G₂) (inj₁ e)   = sizeF G₁ e
sizeF (G₁ |+| G₂) (inj₂ e)   = sizeF G₂ e
sizeF (G₁ |x| G₂) (e₁ , e₂)  = sizeF G₁ e₁ + sizeF G₂ e₂
sizeF (|B| S G)   (x  , y)   = suc (sizeF G y)

size : {F : Functor} → μ F → ℕ
size {F} e = sizeF |R| e

open import Data.Nat.Properties
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

lemmasizeF>0 : {F G : Functor}(e : ⟦ G ⟧ (μ F)) → sizeF G e > 0
lemmasizeF>0 {G = |v| S}      e         = s≤s z≤n
lemmasizeF>0 {G = |1|}        e         = s≤s z≤n
lemmasizeF>0 {F} {|R|}        ⟨ e ⟩     =  lemmasizeF>0 {F} {F} e
lemmasizeF>0 {G = |E| x}      e         = s≤s z≤n
lemmasizeF>0 {G = |Ef| G}     ⟨ e ⟩     = lemmasizeF>0 {G} {G} e
lemmasizeF>0 {G = G₁ |+| G₂}  (inj₁ e)  = lemmasizeF>0 {G = G₁} e
lemmasizeF>0 {G = G₁ |+| G₂}  (inj₂ e)  = lemmasizeF>0 {G = G₂} e
lemmasizeF>0 {G = G₁ |x| G₂}  (e₁ , e₂) =   
  start
    suc zero
  ≤⟨ lemmasizeF>0 {G = G₁} e₁ ⟩
    sizeF G₁ e₁
  ≤⟨ m≤m+n (sizeF G₁ e₁) (sizeF G₂ e₂) ⟩
    (sizeF G₁ e₁) + (sizeF G₂ e₂) 
  ≤⟨ ≤-refl ⟩
    sizeF (G₁ |x| G₂) (e₁ , e₂)
  ◽
lemmasizeF>0 {G = |B| S G}    (x , e)    =
  start
    suc zero 
  ≤⟨ s≤s z≤n ⟩
    suc (suc zero)
  ≤⟨ s≤s (lemmasizeF>0 {G = G} e) ⟩
    1 + sizeF G e
  ≤⟨ ≤-refl ⟩
    sizeF (|B| S G) (x , e)
  ◽
\end{code}


  
  
