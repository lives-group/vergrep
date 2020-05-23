open import Data.List
open import Data.Product
open import Data.String

open import Base.Regex

module Data.RegexContext where

  data LocalCtx : Set where
    InSeqL : Regex -> LocalCtx
    InSeqR : Regex -> LocalCtx
    InAltL : Regex -> LocalCtx
    InAltR : Regex -> LocalCtx
    InRep  : LocalCtx

  RegexCtx = List LocalCtx

  plug : Regex -> LocalCtx -> Regex
  plug e (InSeqL e') = e ∙ e'
  plug e (InSeqR e') = e' ∙ e
  plug e (InAltL e') = e + e'
  plug e (InAltR e') = e' + e
  plug e InRep = e ⋆

  plugCtx : Regex -> RegexCtx -> Regex
  plugCtx = foldl plug

  data Dir : Set where
    Start : Dir
    Finish : Dir

  RegexState : Set
  RegexState = Dir × Regex × RegexCtx
  
