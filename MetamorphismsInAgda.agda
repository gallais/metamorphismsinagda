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
        decon : CoalgListF B g s

  data CoalgListF (B {S} : Set) (g : S → Maybe (B × S)) : S → Set where
    ⟨_⟩    : {s : S} → g s ≡ nothing → CoalgListF B g s
    _∷⟨_⟩_ : (b : B) → {s s' : S} → g s ≡ just (b , s') → CoalgList B g s' → CoalgListF B g s

open CoalgList

left-alg : {A S : Set} → (S → A → S) → A → (S → S) → (S → S)
left-alg _▷_ a t = t ∘ flip _▷_ a

module _ {A B S : Set} where

  module ConsumingBeforeProducing
    (_▷_ : S → A → S) (g : S → Maybe (B × S))
    where

    cbp : (s : S) → {h : S → S} → AlgList A (left-alg _▷_) id h → CoalgList B g (h s)
    decon (cbp s []) with g s        | inspect g s
    decon (cbp s []) | nothing       | [ eq ] = ⟨ eq ⟩
    decon (cbp s []) | just (b , s') | [ eq ] = b ∷⟨ eq ⟩ cbp s' []
    cbp s (a ∷ as) = cbp (s ▷ a) as

  module Streaming
    (_▷_ : S → A → S) (g : S → Maybe (B × S))
    (streaming-condition :
       {a : A} {b : B} {s s' : S} → g s ≡ just (b , s') → g (s ▷ a) ≡ just (b , s' ▷ a))
    where

    streaming-lemma : {b : B} {s s' : S} {h : S → S} →
                      AlgList A (left-alg _▷_) id h → g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
    streaming-lemma []       eq = eq
    streaming-lemma (a ∷ as) eq = streaming-lemma as (streaming-condition eq)

    stream : (s : S) → {h : S → S} → AlgList A (left-alg _▷_) id h → CoalgList B g (h s)
    decon (stream s as      ) with g s        | inspect g s
    decon (stream s []      ) | nothing       | [ eq ] = ⟨ eq ⟩
    decon (stream s (a ∷ as)) | nothing       | [ eq ] = decon (stream (s ▷ a) as)
    decon (stream s as      ) | just (b , s') | [ eq ] = b ∷⟨ streaming-lemma as eq ⟩ stream s' as

  cong-from-just : {X : Set} {x x' : X} → (Maybe X ∋ just x) ≡ just x' → x ≡ x'
  cong-from-just refl = refl

  module Jigsaw-Infinite
    (_◁_ : A → S → S) (e : S) (g∞ : S → B × S)
    (piece : A × B → B × A)
    (jigsaw-conditionᵢ : {a : A} {b : B} {s s' : S} →
                         g∞ s ≡ (b , s') → let (b' , a') = piece (a , b) in g∞ (a ◁ s) ≡ (b' , a' ◁ s'))
    (straight : B) (straight-production : g∞ e ≡ (straight , e))
    where

    fillᵢᵥ : {s : S} → AlgList A _◁_ e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A _◁_ e t × g∞ s ≡ (b , t)
    fillᵢᵥ []       = straight , _ , [] , straight-production
    fillᵢᵥ (a ∷ as) with fillᵢᵥ as
    fillᵢᵥ (a ∷ as) | b , _ , as' , eq = let (b' , a') = piece (a , b)
                                         in  b' , _ , a' ∷ as' , jigsaw-conditionᵢ eq

    jigsawᵢᵥ : {s : S} → AlgList A _◁_ e s → CoalgList B (just ∘ g∞) s
    decon (jigsawᵢᵥ as) with fillᵢᵥ as
    decon (jigsawᵢᵥ as) | b , _ , as' , eq = b ∷⟨ cong just eq ⟩ jigsawᵢᵥ as'
   
    fillᵢₕ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)  
    decon (fillᵢₕ a bs) with decon bs
    decon (fillᵢₕ a bs) | ⟨ () ⟩
    decon (fillᵢₕ a bs) | b ∷⟨ eq ⟩ bs' =
      let (b' , a') = piece (a , b)
      in  b' ∷⟨ cong just (jigsaw-conditionᵢ (cong-from-just eq)) ⟩ fillᵢₕ a' bs'

    jigsawᵢₕ : {s : S} → AlgList A _◁_ e s → CoalgList B (just ∘ g∞) s
    decon (jigsawᵢₕ []) = straight ∷⟨ cong just straight-production ⟩ jigsawᵢₕ []
    jigsawᵢₕ (a ∷ as) = fillᵢₕ a (jigsawᵢₕ as)

  module Jigsaw-General
    (_◁_ : A → S → S) (e : S) (g : S → Maybe (B × S))
    (nothing-from-e : g e ≡ nothing)
    (piece : A × B → B × A)
    (flat? : (a : A) → ({s : S} → g s ≡ nothing → g (a ◁ s) ≡ nothing) ⊎
                       ({s : S} → g (a ◁ s) ≢ nothing))
    (straight : B)
    (jigsaw-condition :
       {a : A} {b : B} {s s' : S} →
       g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (a ◁ s) ≢ nothing × b ≡ straight × s' ≡ s) →
       let (b' , a') = piece (a , b) in g (a ◁ s) ≡ just (b' , a' ◁ s'))
    where

    fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
    decon (fill a bs) with decon bs
    decon (fill a bs) | ⟨ eq ⟩ with flat? a 
    decon (fill a bs) | ⟨ eq ⟩ | inj₁ flat     = ⟨ flat eq ⟩
    decon (fill a bs) | ⟨ eq ⟩ | inj₂ not-flat =
      let (b' , a') = piece (a , straight)
      in  b' ∷⟨ jigsaw-condition (inj₂ (eq , not-flat , refl , refl)) ⟩ fill a' bs
    decon (fill a bs) | b ∷⟨ eq ⟩ bs' =
      let (b' , a') = piece (a , b)
      in  b' ∷⟨ jigsaw-condition (inj₁ eq) ⟩ fill a' bs'

    jigsaw : {s : S} → AlgList A _◁_ e s → CoalgList B g s
    decon (jigsaw []) = ⟨ nothing-from-e ⟩
    jigsaw (a ∷ as) = fill a (jigsaw as)

  module Jigsaw-Left-Infinite
    (_▷_ : S → A → S) (g : S → B × S)
    (piece : B × A → A × B)
    (jigsaw-condition : {a : A} {b : B} {s s' : S} →
                        g s ≡ (b , s') → let (a' , b') = piece (b , a) in  g (s ▷ a) ≡ (b' , s' ▷ a'))
    where

    fillₗᵢ : {s : S} → CoalgList B (just ∘ g) s → (a : A) → CoalgList B (just ∘ g) (s ▷ a)
    decon (fillₗᵢ bs a) with decon bs
    decon (fillₗᵢ bs a) | ⟨ () ⟩
    decon (fillₗᵢ bs a) | b ∷⟨ eq ⟩ bs' =
      let (a' , b') = piece (b , a)
      in  b' ∷⟨ cong just (jigsaw-condition (cong-from-just eq)) ⟩ fillₗᵢ bs' a'

    jigsawₗᵢ : {s : S} → CoalgList B (just ∘ g) s →
              {h : S → S} → AlgList A (left-alg _▷_) id h → CoalgList B (just ∘ g) (h s)
    jigsawₗᵢ bs []       = bs
    jigsawₗᵢ bs (a ∷ as) = jigsawₗᵢ (fillₗᵢ bs a) as
