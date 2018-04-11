\begin{code}
module OccurBind where

open import GPBindings
open import Fresh
open import List.ListProperties

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List hiding (unfold)
open import Data.List.All
open import Data.List.All.Properties
open import Data.List.Any as Any hiding (tail;map)
import Function.Equality as FE
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse
open Any.Membership-≡
\end{code}


\begin{code}
data ∈bF (x : V){F : Functor} : (G : Functor) → ⟦ G ⟧ (μ F) → Set where
   ∈bFEf    :  {G : Functor}{e : ⟦ G ⟧ (μ G)}
               → ∈bF x G e                    →  ∈bF x (|Ef| G )    ⟨ e ⟩
   ∈bFR     :  {e : ⟦ F ⟧ (μ F)}
               → ∈bF x F e                    →  ∈bF x |R|          ⟨ e ⟩            
   ∈bFinj₁  :  {G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}
               → ∈bF x G₁ e                   →  ∈bF x (G₁ |+| G₂)  (inj₁ e) 
   ∈bFinj₂  :  {G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)}
               → ∈bF x G₂ e                   →  ∈bF x (G₁ |+| G₂)  (inj₂ e) 
   ∈bFx₁    :  {G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)}
               → ∈bF x G₁ e₁                  →  ∈bF x (G₁ |x| G₂)  (e₁ , e₂)
   ∈bFx₂    :  {G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)}
               → ∈bF x G₂ e₂                  →  ∈bF x (G₁ |x| G₂)  (e₁ , e₂) 
   ∈bFB≡    :  {G : Functor}{e : ⟦ G ⟧ (μ F)}{S : Sort}
                                              →  ∈bF x (|B| S G)    (x , e)
   ∈bFB     :  {G : Functor}{e : ⟦ G ⟧ (μ F)}{y : V}{S : Sort}
               → ∈bF x G e                    →  ∈bF x (|B| S G)    (y , e)

_∈b_ : {F : Functor}(n : V) → (μ F) → Set
_∈b_ {F} x = ∈bF x {F} |R|

ListOccurBindF : {F : Functor}(G : Functor) → List V → ⟦ G ⟧ (μ F) → Set
ListOccurBindF G xs e = All (λ x → ∈bF x G e) xs

lemma-ListOccurBindF-Ef : {F : Functor}{G : Functor}{xs : List V}{e : ⟦ G ⟧ (μ G)}
  → ListOccurBindF {G} G xs e → ListOccurBindF {F} (|Ef| G) xs ⟨ e ⟩
lemma-ListOccurBindF-Ef ocurr =  tabulate (∈bFEf ∘ (lookup ocurr))

ListOccurBind : {F : Functor} → List V → μ F → Set
ListOccurBind {F} xs e = ListOccurBindF |R| xs e
\end{code}

\begin{code}
-- Inversion lemmas
lemma-inv∈bFEf  : {F G : Functor}{e : ⟦ G ⟧ (μ G)}{x : V}
                → ∈bF x {F} (|Ef| G ) ⟨ e ⟩
                → ∈bF x G e                    
lemma-inv∈bFEf (∈bFEf ∈bF) = ∈bF 
\end{code}

%<*notOccurBind>
\begin{code}
data notOccurBindF (x : V){F : Functor} :
   (G : Functor) → ⟦ G ⟧ (μ F) → Set where
   notOccurBv     :  {m : V}{S : Sort}
                  →  notOccurBindF x (|v| S)      m
   notOccurB1     :  notOccurBindF x |1|          tt
   notOccurBE     :  {B : Set}{b : B}
                  →  notOccurBindF x (|E| B)      b
   notOccurBEf    :  {G : Functor}{e : ⟦ G ⟧ (μ G)}
                  →  notOccurBindF x G e
                  →  notOccurBindF x (|Ef| G )    ⟨ e ⟩
   notOccurBR     :  {e : ⟦ F ⟧ (μ F)}
                  →  notOccurBindF x F e
                  →  notOccurBindF x |R|          ⟨ e ⟩            
   notOccurBinj₁  :  {G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}
                  →  notOccurBindF x G₁ e
                  →  notOccurBindF x (G₁ |+| G₂)  (inj₁ e) 
   notOccurBinj₂  :  {G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)}
                  →  notOccurBindF x G₂ e
                  →  notOccurBindF x (G₁ |+| G₂)  (inj₂ e) 
   notOccurBx     :  {G₁ G₂ : Functor}
                     {e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)}
                  →  notOccurBindF x G₁ e₁
                  →  notOccurBindF x G₂ e₂
                  →  notOccurBindF x (G₁ |x| G₂)  (e₁ , e₂) 
   notOccurBB≢   :  {G : Functor}{e : ⟦ G ⟧ (μ F)}{y : V}{S : Sort}
                  →  x ≢ y → notOccurBindF x G e
                  →  notOccurBindF x (|B| S G)    (y , e)

_notOccurBind_ : {F : Functor}(n : V) → (μ F) → Set
_notOccurBind_ {F} x = notOccurBindF x {F} |R|
\end{code}
%</notOccurBind>

\begin{code}
data notOccurBindExceptF (x : V){F : Functor}{y : V} : (G : Functor)(e : ⟦ G ⟧ (μ F)) → ∈bF y G e → Set where
   notOccurBExceptEf    : {G : Functor}{e : ⟦ G ⟧ (μ G)}{y∈be : ∈bF y G e}
                   → notOccurBindExceptF x G e y∈be            →  notOccurBindExceptF x (|Ef| G ) (⟨ e ⟩) (∈bFEf y∈be)
   notOccurBExceptR     : {e : ⟦ F ⟧ (μ F)}{y∈be : ∈bF y F e}
                  → notOccurBindExceptF x F e y∈be             →  notOccurBindExceptF x |R| (⟨ e ⟩) (∈bFR y∈be)
   notOccurBExceptinj₁  : {G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}{y∈be : ∈bF y G₁ e}
                  → notOccurBindExceptF x G₁ e y∈be            →  notOccurBindExceptF x (G₁ |+| G₂) (inj₁ e) (∈bFinj₁ y∈be)
   notOccurBExceptinj₂  : {G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)}{y∈be : ∈bF y G₂ e}
                  → notOccurBindExceptF x G₂ e y∈be            →  notOccurBindExceptF x (G₁ |+| G₂) (inj₂ e) (∈bFinj₂ y∈be)               
   notOccurBExceptx₁     : {G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)}{y∈be1 : ∈bF y G₁ e₁}
                   → notOccurBindExceptF x G₁ e₁ y∈be1
                   → notOccurBindF x G₂ e₂                     →  notOccurBindExceptF x (G₁ |x| G₂)  (e₁ , e₂) (∈bFx₁ y∈be1)
   notOccurBExceptx₂     : {G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)}{y∈be2 : ∈bF y G₂ e₂}
                   → notOccurBindF x G₁ e₁
                   → notOccurBindExceptF x G₂ e₂ y∈be2         →  notOccurBindExceptF x (G₁ |x| G₂)  (e₁ , e₂) (∈bFx₂ y∈be2)
   notOccurBExceptB≡   : {G : Functor}{e : ⟦ G ⟧ (μ F)}{S : Sort}
                   → notOccurBindF x G e                       →  notOccurBindExceptF x (|B| S G) (y , e) ∈bFB≡
   notOccurBExceptB    : {G : Functor}{e : ⟦ G ⟧ (μ F)}{z : V}{S : Sort}{y∈be : ∈bF y G e}
                   → notOccurBindExceptF x G e y∈be → x ≢ z    →  notOccurBindExceptF x (|B| S G) (z , e) (∈bFB y∈be)

notOccurBindExcept : {F : Functor}{y : V}(x : V)(e : μ F) → y ∈b e → Set
notOccurBindExcept {F} e y∈be = notOccurBindExceptF e {F} |R| y∈be
\end{code}


\begin{code}
-- Inversion lemmas
notOccurBinj₁inv : {x : V}{F G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)} → notOccurBindF x (G₁ |+| G₂) (inj₁ e) → notOccurBindF x G₁ e 
notOccurBinj₁inv (notOccurBinj₁ notOccur) = notOccur

notOccurBinj₂inv : {x : V}{F G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)} → notOccurBindF x (G₁ |+| G₂) (inj₂ e) → notOccurBindF x G₂ e 
notOccurBinj₂inv (notOccurBinj₂ notOccur) = notOccur

notOccurBx₁inv : {x : V}{F G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)} → notOccurBindF x (G₁ |x| G₂) (e₁ , e₂) → notOccurBindF x G₁ e₁ 
notOccurBx₁inv (notOccurBx notOccur₁ notOccur₂) = notOccur₁

notOccurBx₂inv : {x : V}{F G₁ G₂ : Functor}{e₁ : ⟦ G₁ ⟧ (μ F)}{e₂ : ⟦ G₂ ⟧ (μ F)} → notOccurBindF x (G₁ |x| G₂) (e₁ , e₂) → notOccurBindF x G₂ e₂ 
notOccurBx₂inv (notOccurBx notOccur₁ notOccur₂) = notOccur₂

notOccurBBinv : {x y : V}{F G : Functor}{S : Sort}{e : ⟦ G ⟧ (μ F)} → notOccurBindF x (|B| S G) (y , e) → notOccurBindF x G e 
notOccurBBinv (notOccurBB≢ _ notOccur) = notOccur

notOccurBRinv : {x : V}{F : Functor}{e : ⟦ F ⟧ (μ F)} → notOccurBindF x {F} |R| ⟨ e ⟩ → notOccurBindF x F e 
notOccurBRinv (notOccurBR notOccur) = notOccur

notOccurBEfinv : {x : V}{F G : Functor}{e : ⟦ G ⟧ (μ G)} → notOccurBindF x {F} (|Ef| G) ⟨ e ⟩ → notOccurBindF x G e 
notOccurBEfinv (notOccurBEf notOccur) = notOccur

notOccurBBinv≢ : {x y : V}{F G : Functor}{S : Sort}{e : ⟦ G ⟧ (μ F)} → notOccurBindF x (|B| S G) (y , e) → x ≢ y
notOccurBBinv≢ (notOccurBB≢ x≢y _) = x≢y

notOccurBindR→notOccurBindEf : {F F' : Functor}{e : μ F} → ∀ {x} → notOccurBindF x {F} |R| e → notOccurBindF x {F'} (|Ef| F) e
notOccurBindR→notOccurBindEf {e = ⟨ e ⟩} notOccur = notOccurBEf (notOccurBRinv notOccur)

notOccurBindEf→notOccurBindR : {F F' : Functor}{e : μ F} → ∀ {x} → notOccurBindF x {F'} (|Ef| F) e → notOccurBindF x {F} |R| e
notOccurBindEf→notOccurBindR {e = ⟨ e ⟩} notOccur = notOccurBR (notOccurBEfinv notOccur)

--notOccurBindR→notOccurBindF : {F : Functor}{e : ⟦ F ⟧ (μ F)} → ∀ {x} → notOccurBindF x {F} |R| ⟨ e ⟩ → notOccurBindF x {F} F e
--notOccurBindR→notOccurBindF  = notOccurBRinv
\end{code}

%<*listnotocurrbind>
\begin{code}
ListNotOccurBindF  :  {F : Functor}(G : Functor)
                   →  List V → ⟦ G ⟧ (μ F) → Set
ListNotOccurBindF G xs e = All (λ x → notOccurBindF x G e) xs

ListNotOccurBind : {F : Functor} → List V → μ F → Set
ListNotOccurBind {F} xs e = ListNotOccurBindF |R| xs e
\end{code}
%</listnotocurrbind>

\begin{code}
-- Inversion lemmas
lemmalistNotOccurBindEf→ListNotOccurBindR : {F F' : Functor}{e : μ F}{xs : List V}
  → ListNotOccurBindF {F'} (|Ef| F) xs e → ListNotOccurBindF {F} |R| xs e 
lemmalistNotOccurBindEf→ListNotOccurBindR = Data.List.All.map notOccurBindEf→notOccurBindR

lemmalistNotOccurBindFR→ListNotOccurBindEf : {F F' : Functor}{e : μ F}{xs : List V}
  → ListNotOccurBindF {F} |R| xs e → ListNotOccurBindF {F'} (|Ef| F) xs e  
lemmalistNotOccurBindFR→ListNotOccurBindEf = Data.List.All.map notOccurBindR→notOccurBindEf

lemmalistNotOccurBindEf→ListNotOccurBindF : {F G : Functor}{e : ⟦ G ⟧ (μ G)}{xs : List V}
  → ListNotOccurBindF {F} (|Ef| G) xs ⟨ e ⟩ → ListNotOccurBindF {G} G xs e 
lemmalistNotOccurBindEf→ListNotOccurBindF = Data.List.All.map notOccurBEfinv 

lemmalistNotOccurBindFR→ListNotOccurBindF : {F : Functor}{e : ⟦ F ⟧ (μ F)}{xs : List V}
  → ListNotOccurBindF {F} |R| xs ⟨ e ⟩ → ListNotOccurBindF {F} F xs e  
lemmalistNotOccurBindFR→ListNotOccurBindF  = Data.List.All.map notOccurBRinv 

listNotOccurBinj₁inv : {xs : List V}{F G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}
  → ListNotOccurBindF (G₁ |+| G₂) xs (inj₁ e) → ListNotOccurBindF G₁ xs e 
listNotOccurBinj₁inv  =  Data.List.All.map (λ { (notOccurBinj₁ nb) → nb})

listNotOccurBinj₂inv : {xs : List V}{F G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)}
  → ListNotOccurBindF (G₁ |+| G₂) xs (inj₂ e) → ListNotOccurBindF G₂ xs e 
listNotOccurBinj₂inv  =  Data.List.All.map (λ { (notOccurBinj₂ nb) → nb})

listNotOccurBx₁inv : {xs : List V}{F G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}{e' : ⟦ G₂ ⟧ (μ F)}
  → ListNotOccurBindF (G₁ |x| G₂) xs (e , e') → ListNotOccurBindF G₁ xs e 
listNotOccurBx₁inv  =  Data.List.All.map (λ { (notOccurBx nb _) → nb})

listNotOccurBx₂inv : {xs : List V}{F G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}{e' : ⟦ G₂ ⟧ (μ F)}
  → ListNotOccurBindF (G₁ |x| G₂) xs (e , e') → ListNotOccurBindF G₂ xs e' 
listNotOccurBx₂inv  =  Data.List.All.map (λ { (notOccurBx _ nb) → nb})

get : {F : Functor}{xs : List V}{e : μ F} → ListNotOccurBind xs e → (x : V) → x ∈ xs → x notOccurBind e
get nb x x∉xs = lookup nb x∉xs

listNotOccurBBinv : {xs : List V}{F G : Functor}{x : V}{e : ⟦ G ⟧ (μ F)}{S : Sort}
  → ListNotOccurBindF (|B| S G) xs (x , e) → ListNotOccurBindF G xs e
listNotOccurBBinv = Data.List.All.map (λ { (notOccurBB≢ _ nb) → nb}) 

listNotOccurBBinv∉fv : {xs : List V}{F G : Functor}{x : V}{e : ⟦ G ⟧ (μ F)}{S : Sort}
  → ListNotOccurBindF (|B| S G) xs (x , e) → x ∉ xs
listNotOccurBBinv∉fv nb x∈xs with lookup nb x∈xs
... | notOccurBB≢ n≢n _ = ⊥-elim (n≢n refl)

lemma-binds+2 : {F G₁ G₂ : Functor}{e : ⟦ G₂ ⟧ (μ F)}{xs : List V}
                → ListNotOccurBindF G₂ xs e  → ListNotOccurBindF (G₁ |+| G₂) xs (inj₂ e)
lemma-binds+2 notOccur = tabulate (notOccurBinj₂ ∘ (lookup notOccur))

lemma-binds+1 : {F G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}{xs : List V}
                → ListNotOccurBindF G₁ xs e  → ListNotOccurBindF (G₁ |+| G₂) xs (inj₁ e)
lemma-binds+1 notOccur = tabulate (notOccurBinj₁ ∘ (lookup notOccur))

lemma-binds× : {F G₁ G₂ : Functor}{e : ⟦ G₁ ⟧ (μ F)}{e′ : ⟦ G₂ ⟧ (μ F)}{xs : List V}
                 → ListNotOccurBindF G₁ xs e → ListNotOccurBindF G₂ xs e′ → ListNotOccurBindF (G₁ |x| G₂) xs (e , e′)
lemma-binds× noe noe' = tabulate (λ x∈xs → notOccurBx ((lookup noe) x∈xs) ((lookup noe') x∈xs))

lemma-binds1 : {F : Functor}{xs : List V}
               → ListNotOccurBindF {F} |1| xs tt
lemma-binds1 = tabulate (λ _ → notOccurB1)                 

lemma-bindsE : {F : Functor}{A : Set }{a : A}{xs : List V}
                → ListNotOccurBindF {F} (|E| A) xs a
lemma-bindsE = tabulate (λ _ → notOccurBE)

lemma-bindsEf : {F G : Functor}{e : ⟦ F ⟧ (μ F)}{xs : List V}
                 → ListNotOccurBindF F xs e → ListNotOccurBindF {G} (|Ef| F) xs ⟨ e ⟩
lemma-bindsEf notOccur = tabulate (notOccurBEf ∘ (lookup notOccur))

lemma-bindsR : {F  : Functor}{e : ⟦ F ⟧ (μ F)}{xs : List V}
                 → ListNotOccurBindF {F} F xs e → ListNotOccurBindF {F} |R| xs ⟨ e ⟩
lemma-bindsR notOccur = tabulate (notOccurBR ∘ (lookup notOccur))

lemma-bindsB : {F G  : Functor}{e : ⟦ G ⟧ (μ F)}{xs : List V}{S : Sort}{x : V}
               → x ∉ xs → ListNotOccurBindF {F} G xs e → ListNotOccurBindF {F} (|B| S G) xs (x , e)
lemma-bindsB x∉xs notOccur = tabulate (λ y∈xs → notOccurBB≢ (x∉xs∧y∈xs⇒y≢x x∉xs y∈xs) ((lookup notOccur) y∈xs))

lemma-bindsv : {F : Functor}{x : V}{xs : List V}{S : Sort} → ListNotOccurBindF {F} (|v| S) xs x 
lemma-bindsv = tabulate (λ _ → notOccurBv)

lemma-binds:head : {x : V}{xs : List V}{F : Functor}{e : μ F} → ListNotOccurBind (x ∷ xs) e → x notOccurBind e
lemma-binds:head = head

lemma-binds:tail : {x : V}{xs : List V}{F : Functor}{e : μ F} → ListNotOccurBind (x ∷ xs) e → ListNotOccurBind xs e
lemma-binds:tail = tail

lemma-binds:cons : {x : V}{xs : List V}{F : Functor}{e : μ F} → x notOccurBind e → ListNotOccurBind xs e → ListNotOccurBind (x ∷ xs) e
lemma-binds:cons = (_∷_)

lemma-binds++ : {xs ys : List V}{F : Functor}{e : μ F} → ListNotOccurBind xs e → ListNotOccurBind ys e → ListNotOccurBind (xs ++ ys) e
lemma-binds++ {xs} {ys} {F} {e} nxs nys = FE.Π._⟨$⟩_ (to (++↔ {A = V} {P = (λ x → notOccurBindF x |R| e)} {xs = xs} {ys = ys})) (nxs , nys)

lemma-binds++l : {xs ys : List V}{F : Functor}{e : μ F} → ListNotOccurBind (xs ++ ys) e → ListNotOccurBind xs e
lemma-binds++l {xs} {ys} {F} {e} nxs++ys = proj₁ (FE.Π._⟨$⟩_ (from (++↔ {A = V} {P = (λ x → notOccurBindF x |R| e)} {xs = xs} {ys = ys})) nxs++ys)

lemma-binds++r : {xs ys : List V}{F : Functor}{e : μ F} → ListNotOccurBind (xs ++ ys) e → ListNotOccurBind ys e
lemma-binds++r {xs} {ys} {F} {e} nxs++ys = proj₂ (FE.Π._⟨$⟩_ (from (++↔ {A = V} {P = (λ x → notOccurBindF x |R| e)} {xs = xs} {ys = ys})) nxs++ys)

lemma-binds⊆ : {xs ys : List V}{F : Functor}{e : μ F} → ys ⊆ xs → ListNotOccurBind xs e → ListNotOccurBind ys e
lemma-binds⊆ = anti-mono

lemma-foldBindsF : {H F G : Functor}{f : ⟦ F ⟧ (μ H) → μ H}{e : ⟦ G ⟧ (μ F)}{xs : List V}
                   →  ({e  : ⟦ F ⟧ (μ H)} → ListNotOccurBindF F xs e → ListNotOccurBind xs (f e))
                   → ListNotOccurBindF G xs e → ListNotOccurBindF G xs (foldmap F G f e)
lemma-foldBindsF {H} {F} {|1|}      {f} {e}      {xs} prf xs∉e = lemma-binds1
lemma-foldBindsF {H} {F} {|R|}      {f} {⟨ e ⟩}  {xs} prf xs∉e = prf ( lemma-foldBindsF prf (lemmalistNotOccurBindFR→ListNotOccurBindF xs∉e))
lemma-foldBindsF {H} {F} {|E| x}    {f} {e}      {xs} prf xs∉e = lemma-bindsE
lemma-foldBindsF {H} {F} {|Ef| G}   {f} {⟨ e ⟩}  {xs} prf xs∉e = lemma-bindsEf (lemmalistNotOccurBindEf→ListNotOccurBindF xs∉e)
lemma-foldBindsF {H} {F} {G |+| G₁} {f} {inj₁ e} {xs} prf xs∉e = lemma-binds+1 (lemma-foldBindsF prf (listNotOccurBinj₁inv xs∉e))
lemma-foldBindsF {H} {F} {G |+| G₁} {f} {inj₂ e} {xs} prf xs∉e = lemma-binds+2 (lemma-foldBindsF prf (listNotOccurBinj₂inv xs∉e))
lemma-foldBindsF {H} {F} {G |x| G₁} {f} {e}      {xs} prf xs∉e = lemma-binds×  (lemma-foldBindsF prf (listNotOccurBx₁inv xs∉e)) (lemma-foldBindsF prf (listNotOccurBx₂inv xs∉e))
lemma-foldBindsF {H} {F} {|v| S}    {f} {x}      {xs} prf xs∉e = lemma-bindsv
lemma-foldBindsF {H} {F} {|B| S G}  {f} {x , e}  {xs} prf xs∉e = lemma-bindsB (listNotOccurBBinv∉fv xs∉e) (lemma-foldBindsF prf (listNotOccurBBinv xs∉e))

lemma-foldBinds : {H F : Functor}{f : ⟦ F ⟧ (μ H) → μ H}{e : μ F}{xs : List V}
                   →  ({e  : ⟦ F ⟧ (μ H)} → ListNotOccurBindF F xs e → ListNotOccurBind xs (f e))
                   → ListNotOccurBind xs e → ListNotOccurBind xs (fold F f e)
lemma-foldBinds {H} {F} = lemma-foldBindsF {H} {F} {|R|}

lemma-foldCtxBinds : {C H : Functor}{F : Functor}{f : μ C → ⟦ F ⟧ (μ H) → μ H}{c : μ C}{e : μ F}{xs : List V}
                      → ({e  : ⟦ F ⟧ (μ H)} → ListNotOccurBindF F xs e → ListNotOccurBind xs (f c e))
                      → ListNotOccurBind xs e → ListNotOccurBind xs (foldCtx F f c e)
lemma-foldCtxBinds fprf =  lemma-foldBinds fprf
\end{code}
