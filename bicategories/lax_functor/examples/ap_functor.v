Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import bicategory lax_functor two_type.

Definition ap_functor
           `{Univalence}
           {X Y : Type}
           `{IsTrunc 2 X} `{IsTrunc 2 Y}
           (f : X -> Y)
           {x₁ x₂ : X}
  : Functor (oneto (x₁ = x₂)) (oneto (f x₁ = f x₂)).
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - cbn.
    exact (ap f).
  - cbn ; intros p q r.
    induction r.
    reflexivity.
  - cbn ; intros p q r s₁ s₂.
    induction s₁, s₂.
    reflexivity.
  - cbn ; intros p.
    reflexivity.
Defined.

Definition lax_ap_functor
           `{Univalence}
           {X Y : Type}
           `{IsTrunc 2 X} `{IsTrunc 2 Y}
           (f : X -> Y)
  : LaxFunctor (path_bigroupoid X) (path_bigroupoid Y).
Proof.
  simple refine {| Fobj := _ |}.
  - cbn.
    exact f.
  - intros a b ; cbn.
    apply ap_functor.
  - cbn.
    intros a b c.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + cbn ; intros [p q].
      apply (ap_pp f q p)^.
    + intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
      induction r₁, r₂ ; cbn.
      induction p₁, p₂ ; reflexivity.
  - intros a ; cbn.
    reflexivity.
  - intros a b p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros a b p ; cbn.
    induction p ; cbn.
    reflexivity.
  - intros a b c d p q r ; cbn.
    induction p, q, r ; cbn.
    reflexivity.
Defined.