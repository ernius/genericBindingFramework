{- STLC,  nominal syntax -}
\begin{code}
module Examples.STLC where

open import GPBindings

SortTypeVars : Sort
SortTypeVars = 1

SortTermVars : Sort
SortTermVars = 2

tySTLCF : Functor
tySTLCF = |1| |+| |R| |x| |R|                  -- type :- τ | type ⟶ type

tSTLCF : Functor                               -- term :-
tSTLCF = |v| SortTermVars                      --    x
    |+|  |R| |x| |R|                           --  | term term
    |+|  |Ef| tySTLCF |x| |B| SortTermVars |R| --  | λ x : type . term
\end{code}
