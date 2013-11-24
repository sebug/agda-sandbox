module Lambda where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

data Bool : Set where
  true false : Bool

_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
     (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)
     (x : A) → C x (g x)
(f ∘ g) x = f (g x)

data List (A : Set) : Set where
  [] : List A
  _,_ : A → List A → List A

infixr 50 _,_

data Type : Set where
  ι : Type
  _⇒_ : Type → Type → Type

data _≠_ : Type → Type → Set where
  ι≠⇒ : ∀ {σ τ} → ι ≠ (σ ⇒ τ)
  ⇒≠ι : ∀ {σ τ} → (σ ⇒ τ) ≠ ι
  σ1≠σ2 : ∀ {σ1 σ2 τ} → (σ1 ≠ σ2) → (σ1 ⇒ τ) ≠ (σ2 ⇒ τ)
  τ1≠τ2 : ∀ {σ τ1 τ2} → (τ1 ≠ τ2) → (σ ⇒ τ1) ≠ (σ ⇒ τ2)
  neither : ∀ {σ1 σ2 τ1 τ2} → (σ1 ≠ σ2) → (τ1 ≠ τ2) → (σ1 ⇒ τ1) ≠ (σ2 ⇒ τ2)

data Equal? : Type → Type → Set where
  yes : ∀ {τ} → Equal? τ τ
  no  : ∀ {σ τ} → σ ≠ τ → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
ι =?= ι = yes
ι =?= (_ ⇒ _) = no ι≠⇒
(_ ⇒ _) =?= ι = no ⇒≠ι
(σ1 ⇒ τ1) =?= (σ2 ⇒ τ2) with σ1 =?= σ2 | τ1 =?= τ2
(σ1 ⇒ τ1) =?= (.σ1 ⇒ .τ1) | yes | yes = yes
(σ1 ⇒ τ1) =?= (σ2 ⇒ .τ1) | no p | yes = no (σ1≠σ2 p)
(σ1 ⇒ τ1) =?= (.σ1 ⇒ τ2) | yes | no p = no (τ1≠τ2 p)
(σ1 ⇒ τ1) =?= (σ2 ⇒ τ2) | no p | no q = no (neither p q)

data Raw : Set where
  var : ℕ → Raw
  _$_ : Raw → Raw → Raw
  lam : Type → Raw → Raw

Cxt = List Type

data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs} → x ∈ x , xs
  tl : ∀ {y xs} → x ∈ xs → x ∈ y , xs

data Term (Γ : Cxt) : Type → Set where
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ , Γ) τ → Term Γ (σ ⇒ τ)

index : ∀ {A}{x : A}{xs} → x ∈ xs → ℕ
index hd = zero
index (tl p) = suc (index p)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var x) = var (index x)
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

length : ∀ {A} → List A → ℕ
length [] = zero
length (_ , xs) = suc (length xs)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
[] ! n = outside n
x , xs ! zero = inside x hd
x , xs ! suc n with xs ! n
x₁ , xs ! suc .(index p) | inside x p = inside x (tl p)
x , xs ! suc .(length xs + n) | outside n = outside n

data _>_ : ℕ → ℕ → Set where
  s>z : {n : ℕ} → suc n > zero
  s>s : {m n : ℕ} → m > n → suc m > suc n

data BadTerm (Γ : Cxt) : Set where
  bNonFun : Term Γ ι → Raw → BadTerm Γ
  bMismatch : ∀ {σ1 σ2 τ} → Term Γ (σ1 ⇒ τ) → Term Γ σ2 → σ1 ≠ σ2 → BadTerm Γ
  bArg : ∀ {σ τ} → Term Γ (σ ⇒ τ) → BadTerm Γ → BadTerm Γ
  bFun : BadTerm Γ → Raw → BadTerm Γ
  bLam : ∀ {σ} → BadTerm (σ , Γ) → BadTerm Γ
  var : {m : ℕ} → Lookup Γ (length Γ + m) → BadTerm Γ

eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
eraseBad (bNonFun f s) = erase f $ s
eraseBad (bMismatch f s p) = erase f $ erase s
eraseBad (bArg f bt) = erase f $ eraseBad bt
eraseBad (bFun bt x) = eraseBad bt $ x
eraseBad (bLam {σ} bt) = lam σ (eraseBad bt)
eraseBad {Γ} (var {m} _) = var (length Γ + m)

data Infer (Γ : Cxt) : Raw → Set where
  ok : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
  bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) → Infer Γ e
infer Γ (var n) with Γ ! n
infer Γ (var .(index x)) | inside σ x = ok σ (var x)
infer Γ (var .(length Γ + m)) | outside m = bad (var (outside m))
infer Γ (e1 $ e2) with infer Γ e1
infer Γ (.(eraseBad b) $ e2) | bad b = bad (bFun b e2)
infer Γ (.(erase t) $ e2) | ok τ t with infer Γ e2
infer Γ (.(erase t1) $ .(erase t2)) | ok ι t1 | ok τ t2 = bad (bNonFun t1 (erase t2))
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ1 ⇒ τ) t1 | ok σ2 t2 with σ1 =?= σ2
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ1 ⇒ τ) t1 | ok .σ1 t2 | yes = ok τ (t1 $ t2)
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ1 ⇒ τ) t1 | ok σ2 t2 | no reason = bad (bMismatch t1 t2 reason)
infer Γ (.(erase f) $ .(eraseBad b)) | ok ι f | bad b = bad (bNonFun f (eraseBad b))
infer Γ (.(erase t) $ .(eraseBad b)) | ok (σ ⇒ τ) t | bad b = bad (bArg t b)
infer Γ (lam σ e) with infer (σ , Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ .(eraseBad b)) | bad b = bad (bLam b)




