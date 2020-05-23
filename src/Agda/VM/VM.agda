open import Data.Char
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.List.All.Properties
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.Nat       renaming (_+_ to _+N_ ; _≟_ to _≟N_)
open import Data.Product

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


open import Base.Regex
open import BitCoded.BitRegex

module VM.VM where

  Code = List Bit

  -- context
  
  data Hole : Set where
    +-L : Regex -> Hole
    +-R : Regex -> Hole
    :-L : Regex -> Hole
    :-R : Regex -> Hole 
    *   : Hole

  Ctx = List Hole

  -- direction

  data Dir : Set where
    B : Dir
    F : Dir

  eqDirDec : Decidable {A = Dir} _≡_
  eqDirDec B B = yes refl
  eqDirDec B F = no (λ ())
  eqDirDec F B = no (λ ())
  eqDirDec F F = yes refl

  dirLemmaF : ∀ {d} → ¬ (d ≡ F) → d ≡ B
  dirLemmaF {B} neq = refl
  dirLemmaF {F} neq = ⊥-elim (neq refl)

  -- configuration

  infix 3 ⟨_,_,_,_,_⟩

  record Conf : Set where
    constructor ⟨_,_,_,_,_⟩
    field
      dir   : Dir
      rexp  : Regex
      ctx   : Ctx
      code  : Code
      input : List Char

  -- starting configuration

  initConf : Regex -> List Char -> List Conf
  initConf e s = ⟨ B , e , [] , [] , s ⟩ ∷ []


  -- finishing configuration

  data Finishing : Conf -> Set where
    end : ∀ {e bs} -> Finishing ⟨ F , e , [] , bs , [] ⟩

  finishing : ∀ (c : Conf) → Dec (Finishing c)
  finishing ⟨ d , e , ctx , bs , s ⟩ with eqDirDec d F
  finishing ⟨ .F , e , [] , bs , [] ⟩ | yes refl = yes end
  finishing ⟨ .F , e , [] , bs , x ∷ s ⟩ | yes refl = no (λ ())
  finishing ⟨ .F , e , x ∷ ctx , bs , s ⟩ | yes refl = no (λ ())
  finishing ⟨ d  , e , ctx , bs , s ⟩ | no q with dirLemmaF q
  ...| eq rewrite eq = no (λ ())


  -- small step semantics

  data _=>_ : Conf -> Conf -> Set where
    -- starting rules
    Eps : ∀ {c b s} → ⟨ B , ε , c , b , s ⟩ => ⟨ F , ε , c , b , s ⟩
    Chr : ∀ {a s c b} → ⟨ B , # a , c , b , a ∷ s ⟩ => ⟨ F , # a , c , b , s ⟩
    LeftB : ∀ {e e' b c s} → ⟨ B , (e + e') , c , b , s ⟩ => ⟨ B , e , (+-L e' ∷ c) , 0# ∷ b , s ⟩
    RightB : ∀ {e e' b c s} → ⟨ B , (e + e') , c , b , s ⟩ => ⟨ B , e , (+-R e ∷ c) , 1# ∷ b , s ⟩
    CatB : ∀ {e e' b c s} → ⟨ B , e ∙ e' , c , b , s ⟩ => ⟨ B , e , :-L e' ∷ c , b , s ⟩
    Star1 : ∀ {e b c s} → ⟨ B , e ⋆ , c , b , s ⟩ => ⟨ B , e , * ∷ c , 0# ∷ b , s ⟩
    Star2 : ∀ {e b c s} → ⟨ B , e ⋆ , c , b , s ⟩ => ⟨ F , e ⋆ , c , 1# ∷ b , s ⟩
    -- finishing rules
    CatEL : ∀ {e e' b c s} → ⟨ F , e , :-L e' ∷ c , b , s ⟩ => ⟨ B , e' , :-R e ∷ c , b , s ⟩
    CatER : ∀ {e e' b c s} → ⟨ F , e' , :-R e ∷ c , b , s ⟩ => ⟨ F , e ∙ e' , c , b , s ⟩
    LeftE : ∀ {e e' b c s} → ⟨ F , e ,  +-L e' ∷ c , b , s ⟩ => ⟨ F , e + e' , c , 0# ∷ b , s ⟩
    RightE : ∀ {e e' b c s} → ⟨ F , e' , +-R e ∷ c , b , s ⟩ => ⟨ F , e + e' , c , 1# ∷ b , s ⟩ 
    StarE1 : ∀ {e b c s} → ⟨ F , e , * ∷ c , b , s ⟩ => ⟨ B , e , * ∷ c , 0# ∷ b , s ⟩
    StarE2 : ∀ {e b c s} → ⟨ F , e , * ∷ c , b , s ⟩ => ⟨ F , e ⋆ , c , 1# ∷ b , s ⟩


  step : ∀ (c : Conf) -> ∃ (λ cs -> All (λ c' -> c => c') cs)
  step ⟨ B , ∅ , c , b , s ⟩ = , []
  step ⟨ B , ε , c , b , s ⟩ = , Eps ∷ []
  step ⟨ B , # a , c , b , [] ⟩ = , []
  step ⟨ B , # a , c , b , a' ∷ s ⟩ with a ≟ a'
  step ⟨ B , # a , c , b , .a ∷ s ⟩ | yes refl = , Chr ∷ []
  step ⟨ B , # a , c , b , a' ∷ s ⟩ | no p     = , []
  step ⟨ B , e ∙ e' , c , b , s ⟩ = , CatB  ∷ []
  step ⟨ B , e + e' , c , b , s ⟩ = , LeftB  ∷ RightB  ∷ []
  step ⟨ B , e ⋆ , c , b , s ⟩ = , Star1 ∷ Star2 ∷ []
  step ⟨ F , e , [] , b , s ⟩ = , []
  step ⟨ F , e , +-L x ∷ c , b , s ⟩ = , LeftE ∷ []
  step ⟨ F , e , +-R x ∷ c , b , s ⟩ = , RightE  ∷ []
  step ⟨ F , e , :-L x ∷ c , b , s ⟩ = , CatEL ∷ []
  step ⟨ F , e , :-R x ∷ c , b , s ⟩ = , CatER ∷ []
  step ⟨ F , e , * ∷ c , b , s ⟩ = , StarE1  ∷ StarE2 ∷ []

  -- multi step semantics

  data _=>*_ : Conf -> Conf -> Set where
    [] : ∀ {c} -> c =>* c
    _::_ : ∀ {c c' c1} -> c => c1 -> c1 =>* c' -> c =>* c'


  =>2=>* : forall {c : Conf} -> List (∃ (λ cs -> All (_=>_ c) cs)) -> List (∃ (λ cs -> All (_=>*_ c) cs))
  =>2=>* [] = []
  =>2=>* (x ∷ xs) with =>2=>* xs
  =>2=>* ((cx , px) ∷ xs) | xs' = (cx , {!px :: []!}) ∷ xs'

  _+++_ : forall {a b}{A : Set a}{P : A -> Set b}{xs ys} -> All P xs -> All P ys -> All P (xs ++ ys)
  [] +++ ys = ys
  (x ∷ xs) +++ ys = x ∷ (xs +++ ys)


  all-cat : (c : Conf) -> List (∃ (λ cs  -> All (λ c' -> c => c') cs)) -> ∃ (λ cs -> All (λ c' -> c => c') cs)
  all-cat c [] = , []
  all-cat c (p ∷ ps) with all-cat c ps | p
  ...| cs1 , ps1 | pcs , pps = pcs ++ cs1 , (pps +++ ps1)

  steps : (cs : List Conf) -> (c : Conf) -> c ∈ cs ->  ∃ (λ cs' -> All (λ c' -> c =>* c') cs')
  steps .(c ∷ _) c (here refl) = {!!} , {!!}
  steps .(_ ∷ _) c (there pr) = {!!}

  
