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
    (f : A → S → S) (e : S) (g∞ : S → B × S)
    (piece : A × B → B × A)
    (jigsaw-conditionᵢ : {a : A} {b : B} {s s' : S} →
                         g∞ s ≡ (b , s') →
                         let (b' , a') = piece (a , b)
                         in  g∞ (f a s) ≡ (b' , f a' s'))
    (flat-edge : B) (flat-edge-productionᵢ : g∞ e ≡ (flat-edge , e))
    where

    fillᵢᵥ : {s : S} → AlgList A f e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g∞ s ≡ (b , t)
    fillᵢᵥ []       = flat-edge , _ , [] , flat-edge-productionᵢ
    fillᵢᵥ (a ∷ as) with fillᵢᵥ as
    fillᵢᵥ (a ∷ as) | b , _ , as' , eq = let (b' , a') = piece (a , b)
                                         in  b' , _ , a' ∷ as' , jigsaw-conditionᵢ eq

    jigsawᵢᵥ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g∞) s
    decon (jigsawᵢᵥ as) with fillᵢᵥ as
    decon (jigsawᵢᵥ as) | b , _ , as' , eq = b ∷⟨ cong just eq ⟩ jigsawᵢᵥ as'
   
    fillᵢₕ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (f a s)  
    decon (fillᵢₕ a bs) with decon bs
    decon (fillᵢₕ a bs) | ⟨ () ⟩
    decon (fillᵢₕ a bs) | b ∷⟨ eq ⟩ bs' = let (b' , a') = piece (a , b)
                                          in  b' ∷⟨ cong just (jigsaw-conditionᵢ (cong-from-just eq)) ⟩ fillᵢₕ a' bs'

    jigsawᵢₕ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g∞) s
    decon (jigsawᵢₕ []) = flat-edge ∷⟨ cong just flat-edge-productionᵢ ⟩ jigsawᵢₕ []
    jigsawᵢₕ (a ∷ as) = fillᵢₕ a (jigsawᵢₕ as)

  module Jigsaw-General
    (f : A → S → S) (e : S) (g : S → Maybe (B × S))
    (nothing-from-e : g e ≡ nothing)
    (piece : A × B → B × A)
    (flat? : (a : A) → ({s : S} → g s ≡ nothing → g (f a s) ≡ nothing) ⊎ ({s : S} → g (f a s) ≢ nothing))
    (flat-edge : B)
    (jigsaw-condition : {a : A} {b : B} {s s' : S} →
                        g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (f a s) ≢ nothing × b ≡ flat-edge × s' ≡ s) →
                        let (b' , a') = piece (a , b)
                        in  g (f a s) ≡ just (b' , f a' s'))
    where

    fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (f a s)
    decon (fill a bs) with decon bs
    decon (fill a bs) | ⟨ eq ⟩ with flat? a 
    decon (fill a bs) | ⟨ eq ⟩ | inj₁ flat = ⟨ flat eq ⟩
    decon (fill a bs) | ⟨ eq ⟩ | inj₂ not-flat =
      let (b' , a') = piece (a , flat-edge)
      in  b' ∷⟨ jigsaw-condition (inj₂ (eq , not-flat , refl , refl)) ⟩ fill a' bs
    decon (fill a bs) | b ∷⟨ eq ⟩ bs' =
      let (b' , a') = piece (a , b)
      in  b' ∷⟨ jigsaw-condition (inj₁ eq) ⟩ fill a' bs'

    jigsaw : {s : S} → AlgList A f e s → CoalgList B g s
    decon (jigsaw []) = ⟨ nothing-from-e ⟩
    jigsaw (a ∷ as) = fill a (jigsaw as)

-- splitAlgList : {A X : Set} {f : ListF A X → X} {x : X} → AlgList A f x → Σ[ as ∈ List A ] foldr' f as ≡ x
-- splitAlgList         []       = [] , refl
-- splitAlgList {f = f} (a ∷ as) = Product.map (a ∷_) (cong (f ∘ cons a)) (splitAlgList as)

-- forget : {A X : Set} {f : ListF A X → X} {x : X} → AlgList A f x → List A
-- forget = proj₁ ∘ splitAlgList

-- record CoList (B : Set) : Set where
--   coinductive
--   field
--     decon : ListF B (CoList B)

-- -- unfoldr' : {B X : Set} → (X → ListF B X) → X → Colist B
-- -- Colist.decon (unfoldr' g x) with g x
-- -- Colist.decon (unfoldr' g x) | nil       = nil
-- -- Colist.decon (unfoldr' g x) | cons b x' = cons b (unfoldr' g x')

-- -- open Colist

-- -- mutual

-- --   record Bisim {B : Set} (xs ys : Colist B) : Set where
-- --     coinductive
-- --     field
-- --       decon : BisimF B (decon xs) (decon ys)

-- --   data BisimF (B : Set) : ListF B (Colist B) → ListF B (Colist B) → Set where
-- --     nil  : BisimF B nil nil
-- --     cons : {x y : B} {xs ys : Colist B} → x ≡ y → Bisim xs ys → BisimF B (cons x xs) (cons y ys)
    
-- -- _≈_ : {B : Set} → Colist B → Colist B → Set
-- -- _≈_ = Bisim

-- -- module Jigsaw-HorizontalPlacement-Simply-Typed
-- --   {V H S : Set} (f : ListF V S → S) (g : S → H × S)
-- --   (piece : V × H → H × V)
-- --   (h₀ : H)
-- --   (g-h₀ : h₀ ≡ proj₁ (g (f nil)))
-- --   where

-- --   fill : List V → H × List V
-- --   fill []       = h₀ , []
-- --   fill (v ∷ vs) = let (h , vs') = fill vs
-- --                       (h' , v') = piece (v , h)
-- --                   in  h' , v' ∷ vs'

-- --   jigsaw : List V → Colist H
-- --   decon (jigsaw vs) = let (h , vs') = fill vs in cons h (jigsaw vs')

-- --   fill-lemma : (vs : List V) {s : S} →
-- --                foldr' f vs ≡ s →
-- --                let (h , vs') = fill vs
-- --                    (h' , s') = g s
-- --                in  h ≡ h' × jigsaw vs' ≈ unfoldr' (uncurry cons ∘ g) s'
-- --   fill-lemma []       eq = {!!}
-- --   fill-lemma (v ∷ vs) eq = {!!}

-- --   jigsaw-proof : (vs : List V) {s : S} →
-- --                  foldr' f vs ≡ s → jigsaw vs ≈ unfoldr' (uncurry cons ∘ g) s
-- --   Bisim.decon (jigsaw-proof vs eq) = let (heq , bisim) = fill-lemma vs eq
-- --                                      in  cons heq bisim

-- data CoalgListF (A {X} : Set) (T : X → Set) : ListF A X → Set where
--   ⟨_⟩    : {xs : ListF A X} → xs ≡ nil → CoalgListF A T xs
--   _∷⟨_⟩_ : (a : A) {xs : ListF A X} {x' : X} → xs ≡ cons a x' → T x' → CoalgListF A T xs

-- record CoalgList (B {X} : Set) (g : X → ListF B X) (x : X) : Set where
--   coinductive
--   field
--     decon : CoalgListF B (CoalgList B g) (g x)

-- open CoalgList

-- -- Coarser indexing for CoalgList?

-- unfoldr : {B X : Set} → (g : X → ListF B X) (x : X) → CoalgList B g x
-- decon (unfoldr g x) with g x
-- decon (unfoldr g x) | nil       = ⟨ refl ⟩
-- decon (unfoldr g x) | cons b x' = b ∷⟨ refl ⟩ unfoldr g x'

-- record RCoalgList (B {X} : Set) (R : X → ListF B X → Set) (x : X) : Set where
--   coinductive
--   field
--     decon : R x nil ⊎ Σ[ b ∈ B ] Σ[ x' ∈ X ] R x (cons b x') × RCoalgList B R x'

-- mutual

--   data unfoldR-aux {B X : Set} (R : X → ListF B X → Set) (x : X) : ListF B (CoList B) → Set where
--     nil  : R x nil → unfoldR-aux R x nil
--     cons : {b : B} {xs' : CoList B} (x' : X) → R x (cons b x') → unfoldR R x' xs' → unfoldR-aux R x (cons b xs')

--   record unfoldR {B X : Set} (R : X → ListF B X → Set) (x : X) (xs : CoList B) : Set where
--     coinductive
--     field
--       decon : unfoldR-aux R x (CoList.decon xs)

-- open import Data.Nat

-- upFrom : ℕ → CoList ℕ
-- CoList.decon (upFrom n) = cons n (upFrom (suc n))

-- open import Data.Empty

-- sinc-coalg : ℕ → ListF ℕ ℕ → Set
-- sinc-coalg n nil        = ⊥
-- sinc-coalg n (cons m k) = m ≡ n × n <′ k 

-- unfoldR-upFrom : (n : ℕ) → unfoldR sinc-coalg n (upFrom n)
-- unfoldR.decon (unfoldR-upFrom n) = cons (suc n) (refl , ≤′-refl) (unfoldR-upFrom (suc n))

-- upFrom' : ℕ → CoList ℕ
-- CoList.decon (upFrom' n) = cons n (upFrom' (suc (suc n)))

-- unfoldR-upFrom' : (n : ℕ) → unfoldR sinc-coalg n (upFrom' n)
-- unfoldR.decon (unfoldR-upFrom' n) = cons (suc (suc n)) (refl , ≤′-step ≤′-refl) (unfoldR-upFrom' (suc (suc n)))

-- foldl : {A X : Set} → (X → A → X) → X → List A → X
-- foldl f x []       = x
-- foldl f x (a ∷ as) = foldl f (f x a) as

-- foldr : {A X : Set} → (ListF A X → X) → List A → X
-- foldr f []       = f nil
-- foldr f (a ∷ as) = f (cons a (foldr f as))


-- foldl-as-foldr : {A X : Set} (f : X → A → X) (x : X) (as : List A) → foldl f x as ≡ foldr (left-alg f) as x
-- foldl-as-foldr f x []       = refl
-- foldl-as-foldr f x (a ∷ as) = foldl-as-foldr f (f x a) as

-- module Fusion
--   {A X Y : Set} (f : ListF A X → X) (h : X → Y)
--   (g : ListF A Y → Y) (g-nil : g nil ≡ h (f nil))
--   (fusion-condition : {x : X} {y : Y} →
--                       y ≡ h x → {a : A} →
--                       g (cons a y) ≡ h (f (cons a x)))
--   where

--   fusion : {x : X} → AlgList A f x → Σ[ y ∈ Y ] y ≡ h x
--   fusion []       = g nil , g-nil
--   fusion (a ∷ as) with fusion as
--   fusion (a ∷ as) | y , eq = g (cons a y) , fusion-condition eq

-- module ExactFusion
--   {A X Y : Set} (f : ListF A X → X) (h : X → Y)
--   (g : ListF A Y → Y) (g-nil : g nil ≡ h (f nil))
--   (fusion-condition : {y : Y}
--                       {a : A} {x : X} →
--                       y ≡ h x →
--                       Σ[ as ∈ List A ] foldr' f as ≡ x →
--                       g (cons a y) ≡ h (f (cons a x)))
--   where

--   fusion : {x : X} → AlgList A f x → Σ[ y ∈ Y ] y ≡ h x
--   fusion []       = g nil , g-nil
--   fusion (a ∷ as) with fusion as
--   fusion (a ∷ as) | y , eq = g (cons a y) , fusion-condition eq (splitAlgList as)

-- module Baseline
--   {A B S : Set} (f : S → A → S) (g : S → ListF B S)
--   where

--   consume-and-produce : {h : S → S} → AlgList A (left-alg f) h → (s : S) → CoalgList B g (h s)
--   decon (consume-and-produce []       s) with g s
--   decon (consume-and-produce []       s) | nil       = ⟨ refl ⟩
--   decon (consume-and-produce []       s) | cons b s' = b ∷⟨ refl ⟩ consume-and-produce [] s'
--   decon (consume-and-produce (a ∷ as) s) = decon (consume-and-produce as (f s a))

-- -- Left algebraic lists?

-- module Streaming
--   {A B S : Set} (f : S → A → S) (g : S → ListF B S)
--   (streaming-condition : ∀ {s s' b a} → g s ≡ cons b s' → g (f s a) ≡ cons b (f s' a))
--   where

--   streaming-lemma : {s : S} {b : B} {s' : S} {h : S → S} →
--                     AlgList A (left-alg f) h → g s ≡ cons b s' → g (h s) ≡ cons b (h s')
--   streaming-lemma []       eq = eq
--   streaming-lemma (a ∷ as) eq = streaming-lemma as (streaming-condition eq)

--   stream : {h : S → S} → AlgList A (left-alg f) h → (s : S) → CoalgList B g (h s)
--   decon (stream as       s) with g s    | inspect g s
--   decon (stream []       s) | nil       | [ g-s≡nil       ] = ⟨ g-s≡nil ⟩
--   decon (stream (a ∷ as) s) | nil       | [ g-s≡nil       ] = decon (stream as (f s a))
--   decon (stream as       s) | cons b s' | [ g-s≡cons-b-s' ] = b ∷⟨ streaming-lemma as g-s≡cons-b-s' ⟩ stream as s'

-- module Jigsaw-VerticalPlacement
--   {V H S : Set} (f : V → S → S) (e : S) (g : S → H × S)
--   (piece : V × H → H × V)
--   (h₀ : H) (g-h₀ : g e ≡ (h₀ , e))
--   (piece-cond : {v : V} {h : H} {s s' : S} →
--                 let (h' , v') = piece (v , h)
--                 in  g s ≡ (h , s') → g (f v s) ≡ (h' , f v' s'))
--   where
-- 
--   fill : {s : S} → AlgList V f e s → Σ[ h ∈ H ] Σ[ s' ∈ S ] AlgList V f e s' × g s ≡ (h , s')
--   fill []       = h₀ , _ , [] , g-h₀
--   fill (v ∷ vs) with fill vs
--   fill (v ∷ vs) | h , _ , vs' , geq = let (h' , v') = piece (v , h) in h' , _ , v' ∷ vs' , piece-cond geq
-- 
--   jigsaw : {s : S} → AlgList V f e s → CoalgList H (just ∘ g) s
--   decon (jigsaw vs) with fill vs
--   decon (jigsaw vs) | h , _ , vs' , geq = h ∷⟨ cong just geq ⟩ jigsaw vs'

-- cong-uncons : {X Y : Set} {x x' : X} {y y' : Y} → (ListF X Y ∋ cons x y) ≡ cons x' y' → (x , y) ≡ (x' , y')
-- cong-uncons refl = refl

-- module Jigsaw-HorizontalPlacement
--   {V H S : Set} (f : ListF V S → S) (g : S → H × S)
--   (piece : V × H → H × V)
--   (h₀ : H) (g-h₀ : g (f nil) ≡ (h₀ , f nil))
--   (piece-cond : {v : V} {h : H} {s s' : S} →
--                 let (h' , v') = piece (v , h) in g s ≡ (h , s') → g (f (cons v s)) ≡ (h' , f (cons v' s')))
--   where

--   fill : (v : V) {s : S} → CoalgList H (uncurry cons ∘ g) s → CoalgList H (uncurry cons ∘ g) (f (cons v s))
--   decon (fill v     hs) with decon hs 
--   decon (fill v {s} hs) | ⟨ () ⟩
--   decon (fill v     hs) | h ∷⟨ eq ⟩ hs' = let (h' , v') = piece (v , h)
--                                           in  h' ∷⟨ cong (uncurry cons) (piece-cond (cong-uncons eq)) ⟩ fill v' hs'

--   jigsaw : {s : S} → AlgList V f s → CoalgList H (uncurry cons ∘ g) s
--   decon (jigsaw []) = h₀ ∷⟨ cong (uncurry cons) g-h₀ ⟩ jigsaw []
--   jigsaw (v ∷ vs)   = fill v (jigsaw vs)

-- module Jigsaw-FiniteHorizontalPlacement
--   {V H S : Set} (f : ListF V S → S) (g : S → ListF H S)
--   (piece : V × H → H × V)
--   (g-f-nil : g (f nil) ≡ nil)
--   (v₀ : V) (h₀ : H) (_≟v₀ : (v : V) → Dec (v ≡ v₀)) (_≟v₀,h₀ : (vh : V × H) → Dec (vh ≡ (v₀ , h₀)))
--   (g-nil  : {s : S} → g s ≡ nil → g (f (cons v₀ s)) ≡ nil)
--   (g-cons : {s s' : S} → g s ≡ cons h₀ s' → g (f (cons v₀ s)) ≡ nil)
--   (piece-cond-nil  : {s : S} {v : V} → v ≢ v₀ →
--                      let (h' , v') = piece (v , h₀)
--                      in  g s ≡ nil → g (f (cons v s)) ≡ cons h' (f (cons v' s)))
--   (piece-cond-cons : {s s' : S} {v : V} {h : H} → (v , h) ≢ (v₀ , h₀) →
--                      let (h' , v') = piece (v , h)
--                      in  g s ≡ cons h s' → g (f (cons v s)) ≡ cons h' (f (cons v' s')))
--   where

--   fill : (v : V) {s : S} → CoalgList H g s → CoalgList H g (f (cons v s))
--   decon (fill  v  hs) with decon hs
--   decon (fill  v  hs) | ⟨ eq ⟩ with v ≟v₀
--   decon (fill .v₀ hs) | ⟨ eq ⟩ | yes refl = ⟨ g-nil eq ⟩
--   decon (fill  v  hs) | ⟨ eq ⟩ | no  v≢v₀ = let (h' , v') = piece (v , h₀)
--                                             in  h' ∷⟨ piece-cond-nil v≢v₀ eq ⟩ fill v' hs
--   decon (fill  v  hs) |  h  ∷⟨ eq ⟩ hs' with (v , h) ≟v₀,h₀
--   decon (fill .v₀ hs) | .h₀ ∷⟨ eq ⟩ hs' | yes refl      = ⟨ g-cons eq ⟩
--   decon (fill  v  hs) |  h  ∷⟨ eq ⟩ hs' | no  v,h≢v₀,h₀ = let (h' , v') = piece (v , h)
--                                                           in  h' ∷⟨ piece-cond-cons v,h≢v₀,h₀ eq ⟩ fill v' hs'

--   jigsaw : {s : S} → AlgList V f s → CoalgList H g s
--   decon (jigsaw []) = ⟨ g-f-nil ⟩
--   jigsaw (v ∷ vs)   = fill v (jigsaw vs)

-- module Jigsaw-FiniteVerticalPlacement
--   {V H S : Set} (f : ListF V S → S) (g : S → ListF H S)
--   (piece : V × H → H × V)
--   (g-f-nil : g (f nil) ≡ nil)
--   (v₀ : V) (h₀ : H) (_≟v₀ : (v : V) → Dec (v ≡ v₀))
--   (g-nil : {s : S} {v : V} → g s ≡ nil → g (f (cons v s)) ≡ nil)
--   (piece-cond-h₀ : {s : S} {v : V} → v ≢ v₀ →
--                    let (h' , v') = piece (v , h₀) in g (f (cons v s)) ≡ cons h' (f (cons v' (f nil))))
--   (piece-cond-cons : {s s' : S} {v : V} {h : H} →
--                      let (h' , v') = piece (v , h)
--                      in  g s ≡ cons h s' → g (f (cons v s)) ≡ cons h' (f (cons v' s')))
--   where

--   test-and-fill : {s : S} (vs : AlgList V f s) →
--                   □ (_≡ v₀) (forget vs) ⊎ Σ[ h ∈ H ] Σ[ s' ∈ S ] AlgList V f s' × g s ≡ cons h s'
--   test-and-fill []       = inj₁ []
--   test-and-fill (v ∷ vs) with test-and-fill vs
--   test-and-fill (v ∷ vs) | inj₁ all with v ≟v₀
--   test-and-fill (v ∷ vs) | inj₁ all | yes v≡v₀ = inj₁ (v≡v₀ ∷ all)
--   test-and-fill (v ∷ vs) | inj₁ all | no  v≢v₀ = let (h' , v') = piece (v , h₀)
--                                                  in  inj₂ (h' , _ , v' ∷ [] , piece-cond-h₀ v≢v₀)
--   test-and-fill (v ∷ vs) | inj₂ (h , _ , vs' , eq) = let (h' , v') = piece (v , h)
--                                                      in  inj₂ (h' , _ , v' ∷ vs' , piece-cond-cons eq)

--   end-of-production-lemma : {s : S} (vs : AlgList V f s) → □ (_≡ v₀) (forget vs) → g s ≡ nil
--   end-of-production-lemma []       all          = g-f-nil
--   end-of-production-lemma (v ∷ vs) (v≡v₀ ∷ all) = g-nil (end-of-production-lemma vs all)

--   jigsaw : {s : S} → AlgList V f s → CoalgList H g s
--   decon (jigsaw vs) with test-and-fill vs
--   decon (jigsaw vs) | inj₁ all                 = ⟨ end-of-production-lemma vs all ⟩
--   decon (jigsaw vs) | inj₂ (h , s' , vs' , eq) = h ∷⟨ eq ⟩ jigsaw vs'
