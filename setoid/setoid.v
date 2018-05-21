Require Import HoTT.
From GR Require Import polynomial.

(** A `setoid` is an equivalence relation on `A`. *)
Record setoid :=
  Build_setoid { under : Type ;
                 rel : under -> under -> hProp ;
                 refl : forall (x : under), rel x x ;
                 sym : forall (x y : under), rel x y -> rel y x ;
                 trans : forall (x y z : under), rel x y -> rel y z -> rel x z
               }.

Arguments refl { _} _.
Arguments sym {_ _ _} _.
Arguments trans {_ _ _ _} _ _.

Global Instance setoid_reflexive (R : setoid)
  : Reflexive (rel R)
  := @refl R.

Global Instance setoid_symmetry (R : setoid)
  : Symmetric (rel R)
  := @sym R.

Global Instance setoid_transitive (R : setoid)
  : Transitive (rel R)
  := @trans R.

(** Every type induces a setoid by truncating its path space. *)
Definition path_setoid_type (X : Type) : setoid
  := {| under := X ;
        rel := fun x y => merely (x = y) ;
        refl := fun x => tr idpath ;
        sym := fun _ _ => Trunc_rec (fun p => tr p^) ;
        trans := fun _ _ _ p' q' =>
                   Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p'
     |}.

(** Every set induces a setoid via its path space. *)
Definition path_setoid (X : hSet) : setoid
  := {| under := X ;
        rel := fun x y => BuildhProp (x = y) ;
        refl := fun x => idpath ;
        sym := fun _ _ p => p^ ;
        trans := fun _ _ _ p q => p @ q
     |}.

(** Setoids are closed under products. *)
Definition prod_setoid (R₁ : setoid) (R₂ : setoid) : setoid
  := {| under := under R₁ * under R₂ ;
        rel := fun x y =>
                 BuildhProp (rel R₁ (fst x) (fst y) * rel R₂ (snd x) (snd y)) ;
        refl := fun x => (refl (fst x), refl (snd x)) ;
        sym := fun _ _ p => (sym (fst p), sym (snd p)) ;
        trans := fun _ _ _ p q => (trans (fst p) (fst q), trans (snd p) (snd q))
     |}.

(** Setoids are closed under sums. *)
Definition sum_setoid (R₁ : setoid) (R₂ : setoid) : setoid.
Proof.
  unshelve esplit.
  - exact (under R₁ + under R₂).
  - exact (fun x y =>
             match x, y with
             | inl x, inl y => rel R₁ x y
             | inl _, inr _ => BuildhProp Empty
             | inr _, inl _ => BuildhProp Empty
             | inr x, inr y => rel R₂ x y
             end).
  - intros [x | x] ; apply refl.
  - intros [? | ?] [? | ?] ; contradiction || apply sym.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply trans.
Defined.    

(** We can apply polynomial functors to setoids. *)
Fixpoint lift_setoid (R : setoid) (P : polynomial) : setoid
  := match P with
     | poly_var => R
     | poly_const T => path_setoid_type T
     | poly_times P Q => prod_setoid (lift_setoid R P) (lift_setoid R Q)
     | poly_plus P Q => sum_setoid (lift_setoid R P) (lift_setoid R Q)
     end.

(** The function space of setoids. *)
Definition fun_setoid
           (R₁ : setoid) (R₂ : setoid)
           `{Univalence}
  : setoid
  := {| under := {f : under R₁ -> under R₂ & forall (x₁ x₂ : under R₁),
                          rel R₁ x₁ x₂ -> rel R₂ (f x₁) (f x₂)} ;
        rel := fun f g => BuildhProp (forall (x : under R₁), rel R₂ (f.1 x) (g.1 x));
        refl := fun f x => refl (f.1 x) ;
        sym := fun f g p x => sym (p x) ;
        trans := fun f g h p₁ p₂ x => trans (p₁ x) (p₂ x)
     |}.
