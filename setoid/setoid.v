Require Import HoTT.
From GR Require Import polynomial.

(** A `setoid` is an equivalence relation on `A`. *)
Record setoid (A : Type) :=
  Build_setoid { rel : A -> A -> hProp ;
                 refl : forall (x : A), rel x x ;
                 sym : forall (x y : A), rel x y -> rel y x ;
                 trans : forall (x y z : A), rel x y -> rel y z -> rel x z
               }.

Arguments rel {A} _ _ _.
Arguments refl {A _} _.
Arguments sym {A _ _ _} _.
Arguments trans {A _ _ _ _} _ _.

Global Instance setoid_reflexive {A : Type} (R : setoid A)
  : Reflexive (rel R)
  := @refl _ R.

Global Instance setoid_symmetry {A : Type} (R : setoid A)
  : Symmetric (rel R)
  := @sym _ R.

Global Instance setoid_transitive {A : Type} (R : setoid A)
  : Transitive (rel R)
  := @trans _ R.

(** Every type induces a setoid by truncating its path space. *)
Definition path_setoid (X : Type) : setoid X.
Proof.
  unshelve esplit ; simpl.
  - exact (fun x y => merely(x = y)).
  - exact (fun _ => tr idpath).
  - exact (fun _ _ => Trunc_rec (fun p => tr p^)).
  - exact (fun _ _ _ p' q' => Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p').
Defined.

(** Setoids are closed under products. *)
Definition prod_setoid
           {A B : Type} (R₁ : setoid A) (R₂ : setoid B)
  : setoid (A * B)
  := {| rel := fun x y =>
                 BuildhProp (rel R₁ (fst x) (fst y) * rel R₂ (snd x) (snd y)) ;
        refl := fun x => (refl (fst x), refl (snd x)) ;
        sym := fun _ _ p => (sym (fst p), sym (snd p)) ;
        trans := fun _ _ _ p q => (trans (fst p) (fst q), trans (snd p) (snd q))
     |}.

(** Setoids are closed under sums. *)
Definition sum_setoid
           {A B : Type} (R₁ : setoid A) (R₂ : setoid B)
  : setoid (A + B).
Proof.
  unshelve esplit.
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
Definition lift_setoid
           {A : Type} (G : setoid A) (P : polynomial)
  : setoid (poly_act P A).
Proof.
  induction P ; simpl.
  - exact G.
  - exact (path_setoid T).
  - apply prod_setoid ; assumption.
  - apply sum_setoid ; assumption.
Defined.