Require Import HoTT.
Require Import polynomial.

(** A groupoid consists of a relation with a certain structure.
   This relation has two parts.
   First of all, it has objects.
   Second of all, for each pair of objects there is a set of arrows between them.
*)
Definition relation (A : Type) := A -> A -> hSet.

(** Now we can define what a groupoid is.
    In addition to a relation, we also have algebraic structure.
*)
Record groupoid (A : Type) :=
  Build_grpd { hom : relation A ;
               e : forall (x : A), hom x x ;
               inv : forall (x y : A), hom x y -> hom y x ;
               comp : forall (x y z : A), hom x y -> hom y z -> hom x z ;
               ca : forall (x y z v : A) (p : hom x y) (q : hom y z) (r : hom z v),
                   comp _ _ _ p (comp _ _ _ q r) = comp _ _ _ (comp _ _ _ p q) r ;
               ce : forall (x y : A) (p : hom x y), comp x y y p (e y) = p ;
               ec : forall (x y : A) (p : hom x y), comp x x y (e x) p = p ;
               ci : forall (x y : A) (p : hom x y), comp x y x p (inv x y p) = e x ;
               ic : forall (x y : A) (p : hom x y), comp y x y (inv x y p) p = e y ;
             }.

Arguments e {_} {_} _.
Arguments hom {_} _.
Arguments inv {_} {_} {_} {_}.
Notation "p × q" := (comp _ _ _ _ _ p q) (at level 80).

(** Now let's discuss some examples of groupoids.
    The first example is the paths on a certain type.
*)
Definition path_space (X : Type) : X -> X -> hSet
  := fun (x y : X) => BuildhSet (Trunc 0 (x = y)).

Definition path_groupoid (X : Type) : groupoid X.
Proof.
  unshelve esplit ; simpl.
  - exact (path_space X).
  - exact (fun _ => tr idpath).
  - exact (fun _ _ => Trunc_rec (fun p => tr p^)).
  - exact (fun _ _ _ p' q' => Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p').
  - intros ? ? ? ? p q r ; simpl.
    strip_truncations ; simpl.
    exact (ap tr (concat_p_pp p q r)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_p1 p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_1p p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_pV p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_Vp p)).
Defined.

Notation "p · q" := (comp _ (path_groupoid _) _ _ _ p q) (at level 80).

(** Groupoids are closed under products. *)
Definition prod_groupoid
           {A B : Type} (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A * B).
Proof.
  unshelve esplit.
  - exact (fun x y => BuildhSet (hom G₁ (fst x) (fst y) * hom G₂ (snd x) (snd y))).
  - intros ; simpl.
    split ; apply e.
  - intros ? ? [p1 p2] ; simpl.
    exact (inv p1, inv p2).
  - intros ? ? ? [p1 p2] [q1 q2].
    exact (p1 × q1, p2 × q2).
  - intros ? ? ? ? [p1 p2] [q1 q2] [r1 r2].
    apply path_prod ; apply ca.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ce.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ec.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ci.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ic.
Defined.

(** Groupoids are closed under sums. *)
Definition sum_groupoid
           {A B : Type} (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A + B).
Proof.
  unshelve esplit.
  - exact (fun x y =>
             match x, y with
             | inl x, inl y => hom G₁ x y
             | inl _, inr _ => BuildhSet Empty
             | inr _, inl _ => BuildhSet Empty
             | inr x, inr y => hom G₂ x y
             end).
  - intros [x | x] ; apply e.
  - intros [? | ?] [? | ?] ; contradiction || apply inv.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply comp.
  - intros [? | ?] [? | ?] [? | ?] [? | ?] ; try contradiction ; apply ca.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ce.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ec.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ci.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ic.
Defined.    

(** We can apply polynomial functors to groupoids. *)
Definition lift_groupoid
           {A : Type} (G : groupoid A) (P : polynomial)
  : groupoid (poly_act P A).
Proof.
  induction P ; simpl.
  - exact G.
  - exact (path_groupoid T).
  - apply prod_groupoid ; assumption.
  - apply sum_groupoid ; assumption.
Defined.

Definition inv_e
           {A : Type}
           (G : groupoid A)
           (a : A)
  : inv (@e _ G a) = e a
  := (ce _ _ _ _ _)^ @ ic A G _ _ (e a).
