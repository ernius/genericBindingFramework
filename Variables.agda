module Variables where

open import GPBindings
open import Fresh
open import ListProperties

open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product hiding (swap)
open import Data.List
open import Data.Bool
open import Relation.Nullary.Decidable hiding (map)
open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡
open import Relation.Binary.PropositionalEquality hiding ([_])

vars' : {G F : Functor} → ⟦ G ⟧ (μ F) → List V
vars' {|v| S'}   e        = [ e ]
vars' {|1|}      tt       = []
vars' {|E| x}    e        = []
vars' {|Ef|   G} ⟨ e ⟩    = vars' {G} e
vars' {|R|}  {F} ⟨ e ⟩    = vars' {F} e
vars' {F |+| F₁} (inj₁ x) = vars' {F} x
vars' {F |+| F₁} (inj₂ y) = vars' {F₁}y
vars' {F |x| F₁} (x , y)  = vars' {F} x ++ vars' {F₁} y
vars' {|B| S' F} (x , e)  = vars' {F} e

vars : {F : Functor} → μ F → List V
vars {F} ⟨ e ⟩ = vars' {F} {F} e

lemmavars#' : {G F : Functor}{x : V}(e : ⟦ G ⟧ (μ F)) → x ∉ (vars' {G} {F} e) → (S : Sort) → fresh' S x G e
lemmavars#' {|v| S'}    {x = e'} 
                        e          x∉vars S with S' ≟S  S
... | no  S'≢S                        = freshV≢S  S'≢S
lemmavars#' {|v| S}     {x = e'} 
                        e          x∉vars .S
    | yes refl                        with e' ≟v  e
... | no  e'≢e                        = freshV≢ e'≢e
lemmavars#' {|v| S}     {x = .e} 
                        e          x∉[x]  .S
    | yes refl                        
    | yes refl                        = ⊥-elim (lemmax∉[x]absurd x∉[x])
lemmavars#' {|1|}       tt         x∉vars S = fresh1
lemmavars#' {|E| x}     e          x∉vars S = freshE
lemmavars#' {|Ef| G}    ⟨ e ⟩      x∉vars S = freshEf    (lemmavars#' e x∉vars S)
lemmavars#' {|R|}       ⟨ e ⟩      x∉vars S = freshR     (lemmavars#' e x∉vars S) 
lemmavars#' {G |+| G₁}  (inj₁ e)   x∉vars S = freshinj₁  (lemmavars#' e x∉vars S)
lemmavars#' {G |+| G₁}  (inj₂ e)   x∉vars S = freshinj₂  (lemmavars#' e x∉vars S)
lemmavars#' {G |x| G₁}  
                      (e₁ , e₂)    x∉vars S = freshx     (lemmavars#' e₁ (c∉xs++ys→c∉xs x∉vars) S)
                                                         (lemmavars#' e₂ (c∉xs++ys→c∉ys {xs = vars' {G} e₁} x∉vars) S) 
lemmavars#' {|B| S' G}  
                      (a , e)      x∉vars S = freshb (lemmavars#' e x∉vars S)

lemmavars# : {F : Functor}{x : V}{e : μ F} → x ∉ vars e → (S : Sort) → fresh S x e
lemmavars# {e = ⟨ e ⟩} x∉vars S = lemmavars#' e x∉vars S
