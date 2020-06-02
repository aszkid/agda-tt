module Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

open import Function using (_∘_)

open import plfa.part1.Isomorphism using (_≃_; _≲_)

--------------------------------------------------------------------------------
-- Binary strings

-- e.g. four is represented as ⟨⟩ I O O
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = from b * 2
from (b I) = suc (from b * 2)

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

-- Want:

--   ∀ {n : ℕ}   → from (to n) ≡ n
--   ∀ {b : Bin} → to (from b) ≡ b

-- The problem:

_ : from (⟨⟩ O O O O O) ≡ 0
_ = refl

_ : to 0 ≡ ⟨⟩ O
_ = refl

--------------------------------------------------------------------------------
-- from (to n) ≡ n

from-inc=suc-from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
-- <editor-fold>
from-inc=suc-from ⟨⟩ =
  refl
from-inc=suc-from (b O) =
  refl
from-inc=suc-from (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    from (inc b) * 2
  ≡⟨ cong (_* 2) (from-inc=suc-from b) ⟩
    suc (from b) * 2
  ≡⟨⟩
    2 + from b * 2
  ≡⟨⟩
    suc (suc (from b * 2))
  ≡⟨⟩
    suc (from (b I))
  ∎
-- </editor-fold>

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from-inc=suc-from (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-to n) ⟩
    suc n
  ∎

--------------------------------------------------------------------------------
-- Canonical binary strings

-- <editor-fold>
data One : Bin → Set where
  just-one : One (⟨⟩ I)
  add-o : ∀ {b : Bin} → One b → One (b O)
  add-i : ∀ {b : Bin} → One b → One (b I)
-- </editor-fold>

-- A binary string is canonical if...
data Can : Bin → Set where
  just-zero : Can (⟨⟩ O) -- ...it is a single O, or...
  leading-one : ∀ {b : Bin} → One b → Can b -- ...has a leading I

--------------------------------------------------------------------------------
-- Can b → Can (inc b)

-- <editor-fold>
one-inc : ∀ {b : Bin} → One b → One (inc b)
one-inc just-one = add-o just-one
one-inc (add-o one-b) = add-i one-b
one-inc (add-i one-b) = add-o (one-inc one-b)
-- </editor-fold>

can-inc : ∀ {b : Bin} → Can b → Can (inc b)
-- <editor-fold>
can-inc just-zero = leading-one just-one
can-inc (leading-one x) = leading-one (one-inc x)
-- </editor-fold>

--------------------------------------------------------------------------------
-- Can (to n)

to-can : ∀ {n : ℕ} → Can (to n)
-- <editor-fold>
to-can {zero} = just-zero
to-can {suc n} = can-inc (to-can {n})
-- </editor-fold>

--------------------------------------------------------------------------------
-- Can b → to (from b) ≡ b

-- <editor-fold>
1≤One : ∀ {b : Bin} → One b → 1 ≤ from b
1≤One just-one = s≤s z≤n
1≤One (add-o one-b) = ≤-trans (1≤One one-b) ≤-twice
  where
    ≤-suc : ∀ {n : ℕ} → n ≤ suc n
    ≤-suc {zero} = z≤n
    ≤-suc {suc n} = s≤s ≤-suc

    relax : ∀ {m n : ℕ} → m ≤ n → m ≤ suc n
    relax {zero} _ = z≤n
    relax {suc m} {n} m≤n = ≤-trans m≤n ≤-suc

    ≤-twice : ∀ {n : ℕ} → n ≤ n * 2
    ≤-twice {zero} = z≤n
    ≤-twice {suc n} = s≤s (relax (≤-twice {n}))
1≤One (add-i one-b) = s≤s z≤n

*2-lemma : ∀ {n : ℕ} → 1 ≤ n → to (n * 2) ≡ (to n) O
*2-lemma (s≤s (z≤n {n})) = helper n
  where
    helper : ∀ (n : ℕ) → to ((suc n) * 2) ≡ (to (suc n)) O
    helper zero = refl
    helper (suc n) = cong (inc ∘ inc) (helper n)

to-from-one : ∀ {b : Bin} → One b → to (from b) ≡ b
to-from-one just-one = refl
to-from-one (add-o {b} one-b) =
  begin
    to (from b * 2)
  ≡⟨ *2-lemma (1≤One one-b) ⟩
    to (from b) O
  ≡⟨ cong _O (to-from-one one-b) ⟩
    b O
  ∎
to-from-one (add-i {b} one-b) =
  begin
    inc (to (from b * 2))
  ≡⟨ cong inc (*2-lemma (1≤One one-b)) ⟩
    inc (to (from b) O)
  ≡⟨ cong _I (to-from-one one-b) ⟩
    b I
  ∎
-- </editor-fold>

to-from : ∀ {b : Bin} → Can b → to (from b) ≡ b
-- <editor-fold>
to-from just-zero = refl
to-from (leading-one o) = to-from-one o

--------------------------------------------------------------------------------
-- ℕ ≲ Bin

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
    { to = to
    ; from = from
    ; from∘to = from-to
    }

-- </editor-fold>

--------------------------------------------------------------------------------
-- ℕ ≃ ⟨ binary string b , proof b is canonical ⟩
-- ℕ ≃ ∃[ b ](Can b)

-- <editor-fold>
≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'
≡One just-one just-one = refl
≡One (add-o o) (add-o o') = cong add-o (≡One o o')
≡One (add-i o) (add-i o') = cong add-i (≡One o o')
-- </editor-fold>

≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'
-- <editor-fold>
≡Can just-zero just-zero = refl
≡Can just-zero (leading-one (add-o ()))
≡Can (leading-one (add-o ())) just-zero
≡Can (leading-one o) (leading-one o') = cong leading-one (≡One o o')

proj₁≡→Can≡ : ∀ {cb cb' : ∃[ b ](Can b)} → proj₁ cb ≡ proj₁ cb' → cb ≡ cb'
proj₁≡→Can≡ {⟨ b , can-b ⟩} {⟨ b' , can-b' ⟩} refl
  rewrite ≡Can can-b can-b' =
    refl
-- </editor-fold>

ℕ≃∃b-Can : ℕ ≃ ∃[ b ] (Can b)
ℕ≃∃b-Can =
  record
    { to = λ{ n → ⟨ to n , to-can {n} ⟩ }
    ; from = λ{ ⟨ b , _ ⟩ → from b }
    ; from∘to = λ{ n → from-to n }
    ; to∘from = λ{ cb → proj₁≡→Can≡ (to-from (proj₂ cb))}
    }
