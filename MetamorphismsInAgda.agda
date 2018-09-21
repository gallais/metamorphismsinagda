open import Function using (id; _∘_; flip; _∋_)
open import Data.Product as Product
open import Data.Sum
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

foldr : {A S : Set} → (A → S → S) → S → List A → S
foldr _◁_ e []       = e
foldr _◁_ e (a ∷ as) = a ◁ foldr _◁_ e as

foldl : {A S : Set} → (S → A → S) → S → List A → S
foldl _▷_ e []       = e
foldl _▷_ e (a ∷ as) = foldl _▷_ (e ▷ a) as

mutual

  record CoList (B : Set) : Set where
    coinductive
    field
      decon : CoListF B

  data CoListF (B : Set) : Set where
    []  : CoListF B
    _∷_ : B → CoList B → CoListF B

unfoldr : {B S : Set} → (S → Maybe (B × S)) → S → CoList B
CoList.decon (unfoldr g s) with g s
CoList.decon (unfoldr g s) | nothing       = []
CoList.decon (unfoldr g s) | just (b , s') = b ∷ unfoldr g s'

data AlgList (A {S} : Set) (_◁_ : A → S → S) (e : S) : S → Set where
  []  : AlgList A _◁_ e e
  _∷_ : (a : A) → {s : S} → AlgList A _◁_ e s → AlgList A _◁_ e (a ◁ s)

mutual

  record CoalgList (B {S} : Set) (g : S → Maybe (B × S)) (s : S) : Set where
    coinductive
    field
        decon : CoalgListF B g (g s)

  data CoalgListF (B {S} : Set) (g : S → Maybe (B × S)) : Maybe (B × S) → Set where
    []  : CoalgListF B g nothing
    _∷_ : (b : B) → {s' : S} → CoalgList B g s' → CoalgListF B g (just (b , s'))

open CoalgList

from-left-alg : {A S : Set} → (S → A → S) → A → (S → S) → (S → S)
from-left-alg _▷_ a t = t ∘ flip _▷_ a

foldl-as-foldr : {A S : Set} {_▷_ : S → A → S} {e : S}
                 (as : List A) → foldl _▷_ e as ≡ foldr (from-left-alg _▷_) id as e
foldl-as-foldr []       = refl
foldl-as-foldr (a ∷ as) = foldl-as-foldr as

module _ {A B S : Set} where

  module ConsumingBeforeProducing
    (_▷_ : S → A → S) (g : S → Maybe (B × S))
    where

    cbp : (s : S) → {h : S → S} → AlgList A (from-left-alg _▷_) id h → CoalgList B g (h s)
    decon (cbp s []) with g s
    decon (cbp s []) | nothing       = []
    decon (cbp s []) | just (b , s') = b ∷ cbp s' []
    cbp s (a ∷ as) = cbp (s ▷ a) as

  module Streaming
    (_▷_ : S → A → S) (g : S → Maybe (B × S))
    (streaming-condition :
       {a : A} {b : B} {s s' : S} → g s ≡ just (b , s') → g (s ▷ a) ≡ just (b , s' ▷ a))
    where

    streaming-lemma : ∀ {s s' : S} {b} {h : S → S} →
                      AlgList A (from-left-alg _▷_) id h →
                      g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
    streaming-lemma []       eq = eq
    streaming-lemma (a ∷ as) eq = streaming-lemma as (streaming-condition eq)

    stream : (s : S) {h : S → S} → AlgList A (from-left-alg _▷_) id h → CoalgList B g (h s)
    decon (stream s as      ) with g s | inspect g s
    decon (stream s []      ) | nothing | [ eq ] rewrite eq = []
    decon (stream s (a ∷ as)) | nothing | _  = decon (stream (s ▷ a) as)
    decon (stream s as      ) | just (b , s') | [ eq ]
      rewrite streaming-lemma as eq = b ∷ stream s' as

  cong-from-just : {X : Set} {x x' : X} → (Maybe X ∋ just x) ≡ just x' → x ≡ x'
  cong-from-just refl = refl

  module Jigsaw-Infinite
    (_◁_ : A → S → S) (e : S) (g∞ : S → B × S)
    (piece : A × B → B × A)
    (jigsaw-conditionᵢ : ∀ a s →
                         let (b' , a') = piece (a , proj₁ (g∞ s))
                         in g∞ (a ◁ s) ≡ (b' , a' ◁ proj₂ (g∞ s)))
    (straight : B) (straight-production : g∞ e ≡ (straight , e))
    where

    fillᵢₕ : {s : S} → AlgList A _◁_ e s → AlgList A _◁_ e (proj₂ (g∞ s))
    fillᵢₕ []             rewrite straight-production   = []
    fillᵢₕ (_∷_ a {s} as) rewrite jigsaw-conditionᵢ a s = _ ∷ fillᵢₕ as

    jigsawᵢₕ : {s : S} → AlgList A _◁_ e s → CoalgList B (just ∘ g∞) s
    decon (jigsawᵢₕ as) with fillᵢₕ as
    decon (jigsawᵢₕ as) | as' = _ ∷ jigsawᵢₕ as'

    fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)
    decon (fillᵢᵥ a bs) with decon bs
    decon (fillᵢᵥ {s} a bs) | b ∷ bs'
      rewrite jigsaw-conditionᵢ a s = _ ∷ fillᵢᵥ _ bs'

  _<∣>_ : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
  ma@(just _) <∣> _  = ma
  nothing     <∣> ma = ma

  module Jigsaw-General
    (_◁_ : A → S → S) (e : S) (g : S → Maybe (B × S))
    (nothing-from-e : g e ≡ nothing)
    (piece : A × B → B × A)
    (flat? : ∀ a s → (g s ≡ nothing → g (a ◁ s) ≡ nothing) ⊎
                     (Is-just (g (a ◁ s))))
    (straight : B)
    (jigsaw-condition :
       ∀ a s → Is-just (g s <∣> g (a ◁ s)) → let (b , s') = fromMaybe (straight , s) (g s) in -- g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (a ◁ s) ≢ nothing × b ≡ straight × s' ≡ s) →
       let (b' , a') = piece (a , b) in g (a ◁ s) ≡ just (b' , a' ◁ s'))
    where

    fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
    decon (fill {s} a bs) with g s | g (a ◁ s) | jigsaw-condition a s | flat? a s | decon bs
    ... | _ | _ | jg-c | inj₁ flat  | []      rewrite flat refl     = []
    ... | _ | _ | jg-c | inj₂ ¬flat | []      rewrite jg-c ¬flat    = _ ∷ fill _ bs
    ... | _ | _ | jg-c | fla?       | b ∷ bs' rewrite jg-c (just _) = _ ∷ fill _ bs'

    jigsaw : {s : S} → AlgList A _◁_ e s → CoalgList B g s
    decon (jigsaw []) rewrite nothing-from-e = []
    decon (jigsaw (a ∷ as)) = fill a (jigsaw as) .decon

  module Jigsaw-Left-Infinite
    (_▷_ : S → A → S) (g : S → B × S)
    (piece : B × A → A × B)
    (jigsaw-condition : ∀ a s → let (a' , b') = piece (proj₁ (g s) , a) in
                        g (s ▷ a) ≡ (b' , proj₂ (g s) ▷ a'))
    where

    fillₗᵢ : {s : S} → CoalgList B (just ∘ g) s → (a : A) → CoalgList B (just ∘ g) (s ▷ a)
    decon (fillₗᵢ bs a) with decon bs
    decon (fillₗᵢ {s} bs a) | b ∷ bs'
      rewrite jigsaw-condition a s = _ ∷ fillₗᵢ bs' _

    jigsawₗᵢ : {s : S} → CoalgList B (just ∘ g) s →
               {h : S → S} → AlgList A (from-left-alg _▷_) id h →
               CoalgList B (just ∘ g) (h s)
    jigsawₗᵢ bs []       = bs
    jigsawₗᵢ bs (a ∷ as) = jigsawₗᵢ (fillₗᵢ bs a) as
